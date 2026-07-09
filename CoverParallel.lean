import LRATCatcher.Cover

/-!
# `lratcatch-cover-parallel` — emit a parallel-buildable cube-and-conquer proof

Splits a cube-and-conquer run into independent Lean modules so the per-leaf
`native_decide` refutations build *concurrently* (separate `lean` processes —
real OS parallelism, isolated heaps), instead of one monolithic `native_decide`
over the sequential `checkLeaves` fold. A final module composes the parts with
the proved `cover_unsat`; it runs **no** `native_decide` (pure proof-term
application, kernel-checked).

Why module-level and not `Task`-inside-`native_decide`: the latter is sound
(a Task-parallel fold is provably equal to the sequential one) but
`native_decide`'s evaluator does not distribute `Task.spawn` across threads,
so it yields no speedup. Separate processes do.

Usage:
  lratcatch-cover-parallel base.cnf cubes.icnf leafPrefix cover.lrat Name [chunkSize]

`leafPrefix` matches `lratcatch-export` / `lrat_cover_reflect`: leaf `i`'s
certificate is `{leafPrefix}{i}.lrat` (1-based, cube order of the iCNF file).
`chunkSize` (default 1) groups that many leaves into one module = one
`native_decide` (amortizes Lean startup + the per-`native_decide` compile);
chunkSize 1 maximizes parallelism, larger values trade it for less overhead.

Emits under `LRATCatcher/Generated/<Name>/`:
  Base.lean     — `base`, per-chunk cube lists, their concatenation `cubes`
  Chunk<j>.lean — one `native_decide` refuting all leaves of chunk j
  Cover.lean    — `native_decide` refuting the negated-cubes CNF
  Main.lean     — `base_unsat : base.Unsat` via `cover_unsat`, no `native_decide`
  build.sh      — retry wrapper: Lake auto-parallelizes the build, and each retry
                  rebuilds only failed modules, recovering a transient
                  single-module failure that would otherwise fail Main's import

Build (from the package root): `bash LRATCatcher/Generated/<Name>/build.sh`
(Lake auto-parallelizes across all cores; there is no `-j` flag in Lake 5.)

The final statement is `(LRATCatcher.parseDimacs «base contents»).Unsat`, the same
trusted statement as native-mode `lrat_cover_reflect`; the trust base is the
kernel + compiler with one `native_decide` axiom *per chunk module* (visible in
`#print axioms base_unsat`).
-/

open Std.Sat LRATCatcher

def die {α} (msg : String) : IO α := do
  IO.eprintln s!"lratcatch-cover-parallel: {msg}"
  IO.Process.exit 1

def readInput (path : String) : IO String := do
  try IO.FS.readFile path
  catch e => die s!"cannot read '{path}': {e}"

def writeOut (path content : String) : IO Unit := do
  try IO.FS.writeFile path content
  catch e => die s!"cannot write '{path}': {e}"

/-- Open a file for writing, with the same friendly error as `writeOut`. -/
def openOut (path : String) : IO IO.FS.Handle := do
  try IO.FS.Handle.mk path .write
  catch e => die s!"cannot write '{path}': {e}"

/-- Escape a string for embedding as a Lean string literal. Newlines stay
    literal (Lean string literals may span lines); only `\` and `"` need
    escaping, which LRAT/DIMACS text rarely contains. -/
def escLean (s : String) : String :=
  -- Fast path: one scan; LRAT/DIMACS text typically has no `\` or `"`, so the
  -- copies are skipped. Still escapes correctly in the rare case it does.
  if s.any (fun c => c == '"' || c == '\\') then
    (s.replace "\\" "\\\\").replace "\"" "\\\""
  else s

/-- Render one cube as a `Cube` literal term, e.g. `[(3, true), (5, false)]`. -/
def cubeLit (c : Cube) : String :=
  "[" ++ String.intercalate ", " (c.map (fun (v, b) => s!"({v}, {b})")) ++ "]"

/-- Which files one invocation emits: everything (default), the shared
    modules only (`--part shared`: Base/Cover/Main/build.sh — reads no leaf
    certificates), or a chunk range only (`--part LO:HI`, 1-based inclusive —
    reads exactly those chunks' certificates). The range form lets a driver
    generate, build, and delete certificates in waves, so only a wave of
    certificates is ever on disk (mode-A transient-disk operation); every
    invocation must use the same cube file and chunkSize. -/
inductive Part where
  | all | shared | range (lo hi : Nat)

def parsePart (s : String) : Option Part :=
  if s == "shared" then some .shared
  else match s.splitOn ":" with
    | [lo, hi] =>
      match lo.toNat?, hi.toNat? with
      | some l, some h => if l ≥ 1 && l ≤ h then some (.range l h) else none
      | _, _ => none
    | _ => none

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lratcatch-cover-parallel base.cnf cubes.icnf leafPrefix cover.lrat Name [chunkSize] [--part shared|LO:HI]"
  let (posArgs, part) ←
    match args.span (· != "--part") with
    | (pos, ["--part", p]) =>
      match parsePart p with
      | some part => pure (pos, part)
      | none => die s!"bad --part '{p}' (expected 'shared' or 'LO:HI' with 1 ≤ LO ≤ HI)"
    | (pos, []) => pure (pos, Part.all)
    | _ => die usage
  let (baseFile, icnfFile, leafPrefix, coverFile, name, chunk) ←
    match posArgs with
    | [b, i, lp, cv, n]    => pure (b, i, lp, cv, n, 1)
    | [b, i, lp, cv, n, c] => pure (b, i, lp, cv, n, c.toNat?.getD 0)
    | _ => die usage
  if chunk == 0 then die "chunkSize must be ≥ 1"
  -- `name` becomes a Lean namespace component and a path segment, so it must be
  -- a single identifier; reject early with a clear message rather than emitting
  -- a module set that fails to parse or whose path Lake cannot resolve.
  if name.isEmpty || name.front.isDigit || !name.all (fun c => c.isAlpha || c.isDigit || c == '_') then
    die s!"Name '{name}' must be a Lean identifier component (letters, digits, '_'; not digit-initial)"
  let baseStr ← readInput baseFile
  let icnfStr ← readInput icnfFile
  let cubes := (parseICnf icnfStr).toArray
  let n := cubes.size
  if n == 0 then die "no cubes found in iCNF file"
  let numChunks := (n + chunk - 1) / chunk
  let modPrefix := s!"LRATCatcher.Generated.{name}"
  let dir := s!"LRATCatcher/Generated/{name}"
  -- 1-based inclusive [lo, hi] global cube range of chunk j (1-based)
  let chunkRange := fun (j : Nat) => ((j - 1) * chunk + 1, min n (j * chunk))
  -- which chunk modules this invocation emits
  let (chunkLo, chunkHi) ←
    match part with
    | .all => pure (1, numChunks)
    | .shared => pure (1, 0)  -- empty range
    | .range lo hi =>
      if lo > numChunks then
        die s!"--part {lo}:{hi}: only {numChunks} chunk(s) exist"
      else
        pure (lo, min hi numChunks)
  let emitShared := match part with | .range .. => false | _ => true
  let coverStr ← if emitShared then readInput coverFile else pure ""
  -- Fail before writing anything if a leaf certificate is missing, so a bad
  -- `leafPrefix` leaves no confusing partial output.
  if chunkLo ≤ chunkHi then
    for i in [(chunkRange chunkLo).1 : (chunkRange chunkHi).2 + 1] do
      unless (← System.FilePath.pathExists s!"{leafPrefix}{i}.lrat") do
        die s!"leaf certificate not found: {leafPrefix}{i}.lrat"
  try IO.FS.createDirAll dir
  catch e => die s!"cannot create directory '{dir}': {e}"

  -- ---- Base.lean ----
  if emitShared then
    let mut baseParts : Array String :=
      #[s!"import LRATCatcher.Cover\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
        s!"def base : CNF Nat := LRATCatcher.parseDimacs \"{escLean baseStr}\"\n\n"]
    for j in [1:numChunks+1] do
      let (lo, hi) := chunkRange j
      let cs := (List.range (hi + 1 - lo)).map (fun k => cubeLit cubes[lo - 1 + k]!)
      baseParts := baseParts.push s!"def chunkCubes{j} : List Cube := [{String.intercalate ", " cs}]\n"
    -- cubes = chunkCubes1 ++ chunkCubes2 ++ … ++ chunkCubesM. `++` is right-
    -- associative, matching the forall_mem_append nesting in Main; linear to build.
    let cubesExpr := String.intercalate " ++ " ((List.range numChunks).map (fun k => s!"chunkCubes{k+1}"))
    baseParts := baseParts.push s!"\ndef cubes : List Cube := {cubesExpr}\n\nend {modPrefix}\n"
    writeOut s!"{dir}/Base.lean" (String.join baseParts.toList)

  -- ---- Chunk<j>.lean : one native_decide per chunk ----
  for j in [chunkLo:chunkHi+1] do
    let (lo, hi) := chunkRange j
    -- stream each cert straight to the file via a Handle (no giant in-memory
    -- string and no per-cert copies — essential for 49 GB-class cert sets)
    let h ← openOut s!"{dir}/Chunk{j}.lean"
    h.putStr s!"import LRATCatcher.Generated.{name}.Base\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    h.putStr s!"set_option maxHeartbeats 0 in\n"
    h.putStr s!"theorem chunk{j}_ok : ∀ c ∈ chunkCubes{j}, (Cube.leafCNF c base).Unsat :=\n"
    h.putStr s!"  @LRATCatcher.checkLeaves_sound base chunkCubes{j}\n    ["
    for gi in [lo:hi+1] do
      if gi > lo then h.putStr ",\n     "
      h.putStr "\""
      h.putStr (escLean (← readInput s!"{leafPrefix}{gi}.lrat"))
      h.putStr "\""
    h.putStr "]\n    (by native_decide)\n\n"
    h.putStr s!"end {modPrefix}\n"
    h.flush

  if emitShared then
    -- ---- Cover.lean ----
    writeOut s!"{dir}/Cover.lean" <| String.join
      [s!"import LRATCatcher.Generated.{name}.Base\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n",
       s!"set_option maxHeartbeats 0 in\n",
       s!"theorem coverThm : (negCubesCNF cubes).Unsat :=\n",
       s!"  LRATCatcher.checkLratCnf_sound _ \"{escLean coverStr}\" (by native_decide)\n\n",
       s!"end {modPrefix}\n"]

    -- ---- Main.lean : cheap composition, no native_decide ----
    let mut mainParts : Array String :=
      #[s!"import LRATCatcher.Generated.{name}.Base\nimport LRATCatcher.Generated.{name}.Cover\n"]
    for j in [1:numChunks+1] do
      mainParts := mainParts.push s!"import LRATCatcher.Generated.{name}.Chunk{j}\n"
    mainParts := mainParts.push s!"\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    -- comp = forall_mem_append.mpr ⟨chunk1_ok, … ⟨chunk(M-1)_ok, chunkM_ok⟩…⟩,
    -- built in linear time (M-1 openers, then chunkM_ok, then M-1 closers).
    let openers := String.join ((List.range (numChunks - 1)).map
      (fun i => s!"List.forall_mem_append.mpr ⟨chunk{i+1}_ok, "))
    let comp := openers ++ s!"chunk{numChunks}_ok" ++ String.join (List.replicate (numChunks - 1) "⟩")
    mainParts := mainParts.push <| String.join
      [s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n",
       s!"theorem base_unsat : base.Unsat :=\n  LRATCatcher.cover_unsat\n    ({comp})\n    coverThm\n\n",
       s!"#print axioms base_unsat\n\nend {modPrefix}\n"]
    writeOut s!"{dir}/Main.lean" (String.join mainParts.toList)

    -- ---- build.sh : retry wrapper (run from the package root). Lake is
    -- incremental, so each retry rebuilds only the modules that failed; this
    -- recovers a transient single-module build failure that would otherwise
    -- cascade through Main's import (the chunkSize-1 robustness fix).
    let buildLines : List String :=
      ["#!/bin/bash",
       s!"# Build {modPrefix}.Main, retrying transient per-module build failures.",
       "# Run from the package root. Lake is incremental: each retry rebuilds only",
       "# the modules that failed (a transient hiccup on one of many modules would",
       "# otherwise fail the whole build, since Main imports them all).",
       "set -u",
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

  match part with
  | .range lo hi =>
    IO.println s!"lratcatch-cover-parallel: chunks {lo}..{min hi numChunks} of {numChunks} (chunkSize {chunk}) in {dir}/"
  | _ =>
    IO.println s!"lratcatch-cover-parallel: {n} cubes → {numChunks} chunk(s) (chunkSize {chunk}) in {dir}/"
    IO.println s!"  build (retries transient failures): bash {dir}/build.sh   # default 3 attempts"
    IO.println s!"  or directly (no retry):             lake build {modPrefix}.Main:olean"
  return (0 : UInt32)
