import LRATCatcher.Stream

/-!
# `lratcatch-stream-gen` — emit a chunked (resumable) LRAT import as Lean modules

Splits one LRAT certificate into chunks of at most `chunkLines` text lines and
emits one Lean module per chunk, each discharging a single `native_decide`
step check (`stepStart`/`stepMid`/`stepFinish` from `LRATCatcher.Stream`).
Between chunks the checker state crosses module boundaries as a `Snapshot`
(its own module, shared by producer and consumer, so chunk modules stay
mutually independent and Lake builds them in parallel). The certificate file
is consumed **streaming** — at most one chunk of text is in memory — and can
be deleted right after generation (`--delete-cert`): the emitted modules
contain everything the proof needs.

Two modes:

* `chunk` — the certificate is a refutation (ends in the empty clause).
  `Main.lean` composes the steps to `base_unsat : base.Unsat` with one
  `native_decide` axiom per chunk and nothing else.
* `derive` — the certificate is a *derivation* `F ⊢ F′` (no empty clause;
  e.g. a presolve trace). Emits `fprime.cnf` (the derived formula, original
  variable names) for cubing/solving, and `Main.lean` provides
  `deriv_transfer : (externSnap snapM).Unsat → base.Unsat`; refute
  `externSnap snapM` with the cube-and-conquer machinery (`checkCover` /
  `lratcatch-cover-parallel`) and compose.

Usage:
  lratcatch-stream-gen (chunk|derive) base.cnf cert.lrat Name chunkLines
      [--delete-cert] [--pad <v>] [--chain-prev <FullModuleName> <snapDefName>]

`--pad <v>` (derive mode): check against `base ++ [v ∨ ¬v]` (a padding
tautology, highest clause id) and emit `base := <file> ++ padCNF v`, plus
`deriv_transfer'` which peels the pad back off to the unpadded base — the
chained-batch convention where batch i+1's base is batch i's derived formula
plus a fresh padding clause.

`--chain-prev <Mod> <snap>` (derive mode): `base := externSnap Mod.snap`
(a Lean *term*, no file string; `Mod` imported). The tool still reads
`base.cnf` for its streaming pre-check, so the caller must pass the previous
batch's emitted `fprime.cnf`; the generated `native_decide` re-check is the
authority, so a term/file mismatch fails at build time, not soundness.

Emits under `LRATCatcher/Generated/<Name>/`:
  Base.lean     — `base : CNF Nat` (the DIMACS string + parser), `nv`
  Snap<j>.lean  — boundary snapshot `snap<j>` (compact text codec)
  Chunk<j>.lean — one `native_decide` step check
  Main.lean     — pure composition, no `native_decide`
  build.sh      — retry wrapper (transient per-module failures)
  fprime.cnf    — derive mode only: DIMACS of the derived formula

The generator *runs* the resumable checker while splitting, so an invalid
certificate fails here, not at build time; snapshots are additionally
round-tripped through their codec before being written.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT LRATCatcher
open Std.Tactic.BVDecide.LRAT.Internal

def die {α} (msg : String) : IO α := do
  IO.eprintln s!"lratcatch-stream-gen: {msg}"
  IO.Process.exit 1

def readInput (path : String) : IO String := do
  try IO.FS.readFile path
  catch e => die s!"cannot read '{path}': {e}"

def writeOut (path content : String) : IO Unit := do
  try IO.FS.writeFile path content
  catch e => die s!"cannot write '{path}': {e}"

/-- Escape a string for embedding as a Lean string literal (newlines may stay
    literal; only `\` and `"` need escaping, rare in DIMACS/LRAT text). -/
def escLean (s : String) : String :=
  if s.any (fun c => c == '"' || c == '\\') then
    (s.replace "\\" "\\\\").replace "\"" "\\\""
  else s

/-- Read up to `k` complete lines; `""` only at end of file. -/
def readBlock (h : IO.FS.Handle) (k : Nat) : IO String := do
  let mut buf : String := ""
  for _ in [0:k] do
    let line ← h.getLine
    if line.isEmpty then
      break
    buf := buf ++ line
  return buf

/-- The namespace a module lives in: the fully-qualified module name with its
    last `.`-component dropped (e.g. `LRATCatcher.Generated.Batch0.Snap5` ↦
    `LRATCatcher.Generated.Batch0`). Used by `--chain-prev` to qualify the
    previous batch's snapshot def, which lives in the module's namespace. -/
def dropLastComponent (m : String) : String :=
  String.intercalate "." (m.splitOn ".").dropLast

/-- Parse the optional trailing flags after the five positional arguments:
    `--delete-cert`, `--pad <v>`, `--chain-prev <FullModuleName> <snapDefName>`
    (in any order). Returns `(deleteCert, padVar?, chainPrev?)`. -/
partial def parseFlags :
    List String → Bool → Option Nat → Option (String × String) →
    IO (Bool × Option Nat × Option (String × String))
  | [], d, p, c => pure (d, p, c)
  | "--delete-cert" :: rest, _, p, c => parseFlags rest true p c
  | "--pad" :: v :: rest, d, _, c => do
      let some vn := v.toNat? | die s!"--pad expects a number, got '{v}'"
      parseFlags rest d (some vn) c
  | "--chain-prev" :: m :: s :: rest, d, p, _ =>
      if m.isEmpty || s.isEmpty || (m.splitOn ".").dropLast.isEmpty then
        die s!"--chain-prev expects <FullModuleName> <snapDefName>, and FullModuleName must be dotted (got '{m}' '{s}')"
      else parseFlags rest d p (some (m, s))
  | other, _, _, _ => die s!"unrecognized trailing arguments: {other}"

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lratcatch-stream-gen (chunk|derive) base.cnf cert.lrat Name chunkLines [--delete-cert] [--pad <v>] [--chain-prev <FullModuleName> <snapDefName>]"
  let (mode, baseFile, certFile, name, chunkArg, rest) ←
    match args with
    | m :: b :: c :: n :: k :: r => pure (m, b, c, n, k, r)
    | _ => die usage
  let deriveMode ←
    match mode with
    | "chunk" => pure false
    | "derive" => pure true
    | _ => die usage
  let (deleteCert, padV, chainPrev) ← parseFlags rest false none none
  if (padV.isSome || chainPrev.isSome) && !deriveMode then
    die "--pad and --chain-prev are derive-mode only (they peel/replace the base term of a chained derivation)"
  let some chunkLines := chunkArg.toNat? | die "chunkLines must be a number"
  if chunkLines == 0 then die "chunkLines must be ≥ 1"
  if name.isEmpty || name.front.isDigit
      || !name.all (fun c => c.isAlpha || c.isDigit || c == '_') then
    die s!"Name '{name}' must be a Lean identifier component (letters, digits, '_'; not digit-initial)"

  let baseStr ← readInput baseFile
  -- The formula the certificate is checked against. With `--pad v`, append the
  -- padding tautology `[v ∨ ¬v]` (highest clause id) so the internal pre-check
  -- and the emitted `base` term agree with a certificate produced against the
  -- *padded* formula (the chained-batch convention).
  let fileCNF := parseDimacs baseStr
  let cnf := match padV with
    | some v => fileCNF ++ padCNF v
    | none => fileCNF
  let nv := cnf.numLiterals + 1
  let modPrefix := s!"LRATCatcher.Generated.{name}"
  let dir := s!"LRATCatcher/Generated/{name}"
  try IO.FS.createDirAll dir
  catch e => die s!"cannot create directory '{dir}': {e}"

  -- The base term as it is emitted in Base.lean.  Without `--chain-prev` it is
  -- the DIMACS file embedded as a string + parser; with `--chain-prev M s` it
  -- is `externSnap M.s` (M imported, s its snapshot def, in M's namespace) — no
  -- file string embedded.  `baseTermUnpadded` is the term before the optional
  -- padding clause; `deriv_transfer'` peels the pad back off down to it.
  let baseImport := match chainPrev with
    | some (m, _) => s!"import {m}\n"
    | none => ""
  let baseTermUnpadded := match chainPrev with
    | some (m, s) => s!"LRATCatcher.externSnap {dropLastComponent m}.{s}"
    | none => s!"LRATCatcher.parseDimacs \"{escLean baseStr}\""
  let baseTerm := match padV with
    | some v => s!"{baseTermUnpadded} ++ LRATCatcher.padCNF {v}"
    | none => baseTermUnpadded
  -- `--chain-prev`: the base term is the previous batch's derived formula, which
  -- lives only as a Lean term.  The tool re-reads it from `base.cnf` for its
  -- streaming pre-check, so the caller MUST pass the previous batch's emitted
  -- `fprime.cnf` (which equals `externSnap` of that snapshot) as `base.cnf`.
  -- The tool cannot verify the term↔file correspondence across processes; the
  -- authority is the generated modules' `native_decide` re-check, so a mismatch
  -- fails at build time, never soundness.
  let chainNote := match chainPrev with
    | some _ =>
      s!"-- base term = previous batch's derived formula (externSnap of its snapshot);\n" ++
      s!"-- re-checked by native_decide in the Chunk modules, so a term/file mismatch\n" ++
      s!"-- fails at build time, not soundness.\n"
    | none => ""

  -- ---- Base.lean ----
  writeOut s!"{dir}/Base.lean" <| String.join
    [s!"import LRATCatcher.Stream\n{baseImport}\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
     chainNote,
     s!"def base : CNF Nat := {baseTerm}\n\n",
     s!"def nv : Nat := base.numLiterals + 1\n\nend {modPrefix}\n"]

  -- ---- stream the certificate, one chunk at a time ----
  let certH ← try IO.FS.Handle.mk certFile .read
    catch e => die s!"cannot read '{certFile}': {e}"
  let mut f : DefaultFormula nv := CNF.convertLRAT cnf
  let mut j : Nat := 0          -- chunks emitted
  let mut refuted := false
  repeat
    let text ← readBlock certH chunkLines
    if text.isEmpty then
      break
    let acts := parseActions text
    if acts.isEmpty then
      die s!"chunk {j+1}: no parsable LRAT actions (parse error in '{certFile}'?)"
    j := j + 1
    match runChunk f acts 0 with
    | none => die s!"chunk {j} fails the LRAT check"
    | some .refuted =>
      if deriveMode then
        die s!"chunk {j}: the certificate derives the empty clause — a refutation, not a derivation (use chunk mode)"
      if j == 1 then
        die "certificate refutes within the first chunk — no chunking needed (use lrat_reflect, or a smaller chunkLines)"
      writeOut s!"{dir}/Chunk{j}.lean" <| String.join
        [s!"import {modPrefix}.Base\nimport {modPrefix}.Snap{j-1}\n\n",
         s!"namespace {modPrefix}\n\nset_option maxHeartbeats 0 in\n",
         s!"theorem step{j} : LRATCatcher.stepFinish nv snap{j-1}\n",
         s!"    (LRATCatcher.parseActions \"{escLean text}\") = true := by native_decide\n\n",
         s!"end {modPrefix}\n"]
      refuted := true
      let trailing ← readBlock certH 1
      unless trailing.isEmpty do
        IO.eprintln s!"lratcatch-stream-gen: warning: certificate lines after the refutation in chunk {j} are ignored"
      break
    | some (.more f') =>
      let snap := serialize f'
      let snapStr := printSnap snap
      unless parseSnap snapStr == snap do
        die s!"internal error: snapshot {j} fails its codec round-trip"
      writeOut s!"{dir}/Snap{j}.lean" <| String.join
        [s!"import LRATCatcher.Stream\n\nnamespace {modPrefix}\n\n",
         s!"def snap{j} : LRATCatcher.Snapshot := LRATCatcher.parseSnap \"{escLean snapStr}\"\n\n",
         s!"end {modPrefix}\n"]
      let step :=
        if j == 1 then
          s!"theorem step1 : LRATCatcher.stepStart base\n" ++
          s!"    (LRATCatcher.parseActions \"{escLean text}\") snap1 = true := by native_decide\n"
        else
          s!"theorem step{j} : LRATCatcher.stepMid nv snap{j-1}\n" ++
          s!"    (LRATCatcher.parseActions \"{escLean text}\") snap{j} = true := by native_decide\n"
      let imports :=
        if j == 1 then s!"import {modPrefix}.Base\nimport {modPrefix}.Snap1\n"
        else s!"import {modPrefix}.Base\nimport {modPrefix}.Snap{j-1}\nimport {modPrefix}.Snap{j}\n"
      writeOut s!"{dir}/Chunk{j}.lean" <| String.join
        [imports, s!"\nnamespace {modPrefix}\n\nset_option maxHeartbeats 0 in\n",
         step, s!"\nend {modPrefix}\n"]
      f := f'

  let m := j
  if m == 0 then die s!"'{certFile}' is empty"
  if !deriveMode && !refuted then
    die "certificate ends without deriving the empty clause — a derivation, not a refutation (use derive mode)"

  -- ---- derive mode: the derived formula, for cubing and solving ----
  if deriveMode then
    let fp := externSnap (serialize f)
    unless dimacsRoundTrip fp do
      die "internal error: fprime.cnf fails the DIMACS round-trip self-check"
    writeOut s!"{dir}/fprime.cnf" fp.dimacs

  -- ---- Main.lean : pure composition, no native_decide ----
  let mut inner : String := ""
  if deriveMode then
    if m == 1 then
      inner := "LRATCatcher.stepStart_extern step1 hx"
    else
      inner := s!"(LRATCatcher.stepMid_extern step{m} hx)"
      for k in [2:m] do
        let i := m + 1 - k   -- m-1 down to 2
        inner := s!"(LRATCatcher.stepMid_sound step{i} {inner})"
      inner := s!"LRATCatcher.stepStart_sound step1 {inner}"
  else
    inner := s!"(LRATCatcher.stepFinish_sound step{m})"
    for k in [2:m] do
      let i := m + 1 - k
      inner := s!"(LRATCatcher.stepMid_sound step{i} {inner})"
    inner := s!"LRATCatcher.stepStart_sound step1 {inner}"
  let mut mainParts : Array String := #[]
  for i in [1:m+1] do
    mainParts := mainParts.push s!"import {modPrefix}.Chunk{i}\n"
  if deriveMode && m ≥ 1 then
    mainParts := mainParts.push s!"import {modPrefix}.Snap{m}\n"
  mainParts := mainParts.push s!"\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
  mainParts := mainParts.push "set_option maxRecDepth 1000000 in\n"
  if deriveMode then
    mainParts := mainParts.push <| String.join
      [s!"/-- Certified derivation: any refutation of the derived formula\n",
       s!"    `externSnap snap{m}` (see `fprime.cnf`) refutes `base`. -/\n",
       s!"theorem deriv_transfer (hx : (LRATCatcher.externSnap snap{m}).Unsat) : base.Unsat :=\n",
       s!"  {inner}\n\n#print axioms deriv_transfer\n\n"]
    -- With `--pad`, also expose the transfer to the *unpadded* base term, so a
    -- downstream chain sees the base without the padding tautology clause.
    if padV.isSome then
      mainParts := mainParts.push <| String.join
        [s!"/-- The padding tautology peeled off: refuting `externSnap snap{m}`\n",
         s!"    refutes the unpadded base. -/\n",
         s!"theorem deriv_transfer' (hx : (LRATCatcher.externSnap snap{m}).Unsat) :\n",
         s!"    ({baseTermUnpadded}).Unsat :=\n",
         s!"  LRATCatcher.unsat_of_append_pad (deriv_transfer hx)\n\n",
         s!"#print axioms deriv_transfer'\n\n"]
    mainParts := mainParts.push s!"end {modPrefix}\n"
  else
    mainParts := mainParts.push <| String.join
      [s!"theorem base_unsat : base.Unsat :=\n  {inner}\n\n",
       s!"#print axioms base_unsat\n\nend {modPrefix}\n"]
  writeOut s!"{dir}/Main.lean" (String.join mainParts.toList)

  -- ---- build.sh : retry wrapper (Lake is incremental; retries rebuild only
  -- failed modules — recovers transient single-module failures) ----
  let buildLines : List String :=
    ["#!/bin/bash",
     s!"# Build {modPrefix}.Main, retrying transient per-module build failures.",
     "# Run from the package root.",
     "set -u",
     "# wide generated compositions can overflow the OS thread stack during",
     "# elaboration (exit 134); an unlimited stack is the first remedy",
     "ulimit -s unlimited 2>/dev/null || true",
     s!"TARGET=\"{modPrefix}.Main\"",
     "ATTEMPTS=\"${1:-}\"; [ -z \"$ATTEMPTS\" ] && ATTEMPTS=3",
     "i=1",
     "while [ \"$i\" -le \"$ATTEMPTS\" ]; do",
     "  if lake build \"$TARGET:olean\"; then echo \"build.sh: $TARGET OK (attempt $i)\"; exit 0; fi",
     "  echo \"build.sh: attempt $i failed; retrying (rebuilds only failed modules)\" 1>&2",
     "  i=$((i+1))",
     "done",
     "echo \"build.sh: FAILED after $ATTEMPTS attempts\" 1>&2; exit 1"]
  writeOut s!"{dir}/build.sh" (String.intercalate "\n" buildLines ++ "\n")

  if deleteCert then
    try IO.FS.removeFile certFile
    catch e => die s!"cannot delete '{certFile}': {e}"

  let kind := if deriveMode then "derivation" else "refutation"
  IO.println s!"lratcatch-stream-gen: {kind}, {m} chunk(s) (≤ {chunkLines} lines each) in {dir}/"
  if deriveMode then
    IO.println s!"  derived formula: {dir}/fprime.cnf  (cube + refute it, then compose with deriv_transfer)"
  if deleteCert then
    IO.println s!"  certificate '{certFile}' deleted (modules are self-contained)"
  IO.println s!"  build (retries transient failures): bash {dir}/build.sh"
  IO.println s!"  or directly (no retry):             lake build {modPrefix}.Main:olean"
  return 0
