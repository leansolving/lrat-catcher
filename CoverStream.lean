import LRATCatcher.Cover

/-!
# `lratcatch-cover-stream` — emit a *nested* streaming cube-and-conquer proof

Two-level (nested) cube-and-conquer, imported through **streamed, zstd-compressed**
certificates. The top level splits `base` into top cubes; some of those cubes were
too hard and got *re-cubed* into subcubes (a second level). Each leaf certificate
is checked while it streams from a FIFO (never stored uncompressed), via the
`lrat_stream_cnf` command from `LRATCatcher.StreamOracle`; the final module composes
everything with the proved `cover_unsat` (no `native_decide` — pure proof term).

Compared to `lratcatch-cover-parallel`:

* leaf refutations stream from a compressed archive instead of being embedded as
  string literals — oleans stay small, certificates stay compressed on disk;
* a leaf may itself be a whole sub-cover: for each re-cubed top cube `i` a
  `Parent<i>` module refutes each subcube's leaf (streamed) and its own sub-cover
  cert (embedded, small), then composes them into `(leafCNF cube<i> base).Unsat`.

## Structure of the two levels

* Top cubes `cube1 … cubeN` (canonical iCNF order, matching the top cover cert).
* For a **direct** cube `i`: `leaf<i>_unsat : (leafCNF cube<i> base).Unsat`, streamed.
* For a **re-cubed** (parent) cube `i`: subcubes `sub<i>_1 … sub<i>_M` (δ-only cubes
  over the leaf, canonical order of that parent's sub-cover cert). The streamed
  statement per subcube is `(leafCNF cube<i> base) ++ (toCNF sub<i>_k)` — the
  parent-leaf-then-subunit order the re-cubing pipeline produced — transferred by
  `unsat_append_comm` to `(leafCNF sub<i>_k (leafCNF cube<i> base)).Unsat`, then
  composed with the sub-cover cert `cover<i>` into `parent<i>_unsat`.

## Global module numbering (for `--part`)

Chunk modules are numbered `1 … numChunks` (in cube order), then parent modules
`numChunks+1 … numChunks+numParents` (parents in ascending cube index). `--part LO:HI`
emits exactly the modules whose global number is in `[LO, HI]`; `--part shared` emits
only Base/Cover/Main/build.sh/driver.sh/streams.tsv.

## Streaming at build time

The generated modules name FIFO paths but never create them; `driver.sh` (emitted
alongside `build.sh`) `mkfifo`s each stream path listed in `streams.tsv` and spawns a
`zstd -dc <archive>/<file>.lrat.zst > <fifo>` feeder, then `lake build`s the modules of
a wave, then cleans up. Archive naming: direct leaf `i` → `leaf<i>.lrat.zst`, subleaf
`k` of parent `i` → `leaf<i>_<k>.lrat.zst`.

Usage:
  lratcatch-cover-stream base.cnf cubes.icnf cover.lrat recubed.txt \
    subicnfdir negsubdir streamdir Name [K] [--part shared|LO:HI] [--rel]

`--rel`: the top cover certificate refutes `base ++ negCubesCNF cubes` (a cover
that is exhaustive only *relative to* the base, the shape lookahead cubing tools
produce); `Cover.lean` then states `(base ++ negCubesCNF cubes).Unsat` and
`Main.lean` composes with `cover_unsat_rel`. Solve the cover certificate against
the concatenated DIMACS with the base clauses FIRST, so LRAT clause ids line up.

`recubed.txt`: one `leaf<i>` per line (1-based top-cube index) — the re-cubed cubes.
`subicnfdir/leaf<i>_d8.icnf`: subcube 'a' lines (δ-only) for parent `i`.
`negsubdir/leaf<i>_negsub.lrat`: the sub-cover cert for parent `i` (embedded).
`streamdir`: a path *prefix* used verbatim in the generated `lrat_stream_cnf` commands.
`K` (default 16): direct leaves per chunk module.

The final statement is `(LRATCatcher.parseDimacs «base contents»).Unsat`; the trust base
is kernel + compiler with one `native_decide` axiom per streaming/native module (visible
in `#print axioms base_unsat`).
-/

open Std.Sat LRATCatcher

def die {α} (msg : String) : IO α := do
  IO.eprintln s!"lratcatch-cover-stream: {msg}"
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

/-- Escape a string for embedding as a Lean string literal (only `\` and `"`). -/
def escLean (s : String) : String :=
  if s.any (fun c => c == '"' || c == '\\') then
    (s.replace "\\" "\\\\").replace "\"" "\\\""
  else s

/-- Render one cube as a `Cube` literal term, e.g. `[(3, true), (5, false)]`. -/
def cubeLit (c : Cube) : String :=
  "[" ++ String.intercalate ", " (c.map (fun (v, b) => s!"({v}, {b})")) ++ "]"

/-- Build a `∀ c ∈ [x₁,…,xₙ], p c` proof term from per-element proof strings,
    as a right-nested `List.forall_mem_cons.mpr ⟨hᵢ, …⟩` chain terminated by
    `List.forall_mem_nil _`. Linear in the number of elements. -/
def forallMemProof (elems : List String) : String :=
  elems.foldr (fun e acc => s!"List.forall_mem_cons.mpr ⟨{e}, {acc}⟩") "List.forall_mem_nil _"

/-- Maximum number of segments joined in ONE right-nested `++` expression (and
    in the matching `forall_mem_append` proof chain). Nesting depth is linear
    in the segment count and the elaborator overflows its stack at a few
    thousand (observed: 4,882 segments die, 1,348 pass); above this bound the
    generator emits a two-level grouping (`cubesGrp<t>` defs + per-group
    lemmas), giving depth ≤ `segGroup` at both levels (supports up to
    `segGroup²` = 65,536 segments). -/
def segGroupDefault : Nat := 256

/-- Split a list into consecutive blocks of `g`. -/
partial def blocksOf {α} (g : Nat) (l : List α) : List (List α) :=
  if l.length ≤ g then [l]
  else
    let (h, t) := l.splitAt g
    h :: blocksOf g t

/-- Left-nested `List.forall_mem_append.mpr ⟨⟨…⟩, pₙ⟩` chain matching the
    LEFT-associated `s₁ ++ s₂ ++ …` segment expression (`++` is `infixl`, so
    `s₁ ++ s₂ ++ s₃` is `(s₁ ++ s₂) ++ s₃` and the top split is
    ⟨prefix, last⟩). -/
def appendChain (ps : List String) : String :=
  match ps with
  | [] => "List.forall_mem_nil _"
  | p :: rest => rest.foldl (fun acc q => s!"List.forall_mem_append.mpr ⟨{acc}, {q}⟩") p

/-- Which modules one invocation emits (global numbering: chunks then parents). -/
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

/-- Is the module with the given 1-based global number emitted under this part? -/
def Part.emits : Part → Nat → Bool
  | .all, _ => true
  | .shared, _ => false
  | .range lo hi, g => lo ≤ g && g ≤ hi

/-- Parse `recubed.txt`: one `leaf<i>` per line → set of 1-based indices. -/
def parseRecubed (s : String) : IO (List Nat) := do
  let mut out : List Nat := []
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "c" then continue
    unless t.startsWith "leaf" do
      die s!"recubed.txt: unrecognized line (expected 'leaf<i>'): '{t}'"
    match (t.drop 4).toNat? with
    | some i => out := i :: out
    | none => die s!"recubed.txt: cannot parse leaf index in '{t}'"
  return out.reverse

/-- Read a parent's subcube iCNF as an array of δ-only cubes. -/
def readSubCubes (subicnfDir : String) (i : Nat) : IO (Array Cube) := do
  let p := s!"{subicnfDir}/leaf{i}_d8.icnf"
  let s ← readInput p
  let cs := (parseICnf s).toArray
  if cs.size == 0 then die s!"no subcubes found in '{p}'"
  return cs

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lratcatch-cover-stream base.cnf cubes.icnf cover.lrat recubed.txt subicnfdir negsubdir streamdir Name [K] [--part shared|LO:HI] [--rel]\n  global module numbering: chunk modules 1..numChunks, then parent modules numChunks+1..\n  --rel: the top cover cert refutes base ++ negcubes (relative cover); composes via cover_unsat_rel"
  let relMode := args.contains "--rel"
  let args := args.filter (· != "--rel")
  let (args, segGroup) ←
    match args.span (· != "--seg-group") with
    | (pre, "--seg-group" :: g :: post) =>
      match g.toNat? with
      | some n => if n ≥ 2 then pure (pre ++ post, n)
                  else die "--seg-group must be ≥ 2"
      | none => die s!"bad --seg-group '{g}'"
    | _ => pure (args, segGroupDefault)
  let (posArgs, part) ←
    match args.span (· != "--part") with
    | (pos, ["--part", p]) =>
      match parsePart p with
      | some part => pure (pos, part)
      | none => die s!"bad --part '{p}' (expected 'shared' or 'LO:HI' with 1 ≤ LO ≤ HI)"
    | (pos, []) => pure (pos, Part.all)
    | _ => die usage
  let (baseFile, icnfFile, coverFile, recubedFile, subicnfDir, negsubDir, streamDir, name, kChunk) ←
    match posArgs with
    | [b, i, cv, rc, sd, nd, st, n]    => pure (b, i, cv, rc, sd, nd, st, n, 16)
    | [b, i, cv, rc, sd, nd, st, n, k] => pure (b, i, cv, rc, sd, nd, st, n, k.toNat?.getD 0)
    | _ => die usage
  if kChunk == 0 then die "K (chunk size) must be ≥ 1"
  if name.isEmpty || name.front.isDigit || !name.all (fun c => c.isAlpha || c.isDigit || c == '_') then
    die s!"Name '{name}' must be a Lean identifier component (letters, digits, '_'; not digit-initial)"

  let baseStr ← readInput baseFile
  let icnfStr ← readInput icnfFile
  let cubes := (parseICnf icnfStr).toArray
  let n := cubes.size
  if n == 0 then die "no cubes found in iCNF file"

  -- ---- re-cubed (parent) set ----
  let recubedStr ← readInput recubedFile
  let recubedList ← parseRecubed recubedStr
  let mut recubed : Array Bool := Array.replicate (n + 1) false
  for i in recubedList do
    if i < 1 || i > n then die s!"recubed.txt: leaf{i} out of range 1..{n}"
    recubed := recubed.set! i true
  -- parents in ascending cube-index order
  let mut parents : Array Nat := #[]
  for i in [1:n+1] do
    if recubed[i]! then parents := parents.push i
  let numParents := parents.size

  -- ---- segmentation: maximal direct runs (chunked by K) interleaved with parents ----
  -- items: `.inl run` (consecutive direct indices) | `.inr i` (a parent cube index)
  let mut items : Array (Sum (Array Nat) Nat) := #[]
  let mut run : Array Nat := #[]
  for i in [1:n+1] do
    if recubed[i]! then
      if run.size > 0 then items := items.push (.inl run); run := #[]
      items := items.push (.inr i)
    else
      run := run.push i
  if run.size > 0 then items := items.push (.inl run)
  -- chunk each direct run into K-sized chunks; record the ordered segment list
  -- segOrder: `.inl j` (1-based chunk id) | `.inr i` (parent cube index)
  let mut chunks : Array (Array Nat) := #[]
  let mut segOrder : Array (Sum Nat Nat) := #[]
  for it in items do
    match it with
    | .inr i => segOrder := segOrder.push (.inr i)
    | .inl r =>
      let mut off := 0
      while off < r.size do
        let chunk := r.extract off (min r.size (off + kChunk))
        chunks := chunks.push chunk
        segOrder := segOrder.push (.inl chunks.size)
        off := off + kChunk
  let numChunks := chunks.size
  let totalMods := numChunks + numParents

  -- validate --part range against the global module count
  match part with
  | .range lo _ => if lo > totalMods then die s!"--part {lo}:..: only {totalMods} module(s) exist (chunks 1..{numChunks}, parents {numChunks+1}..{totalMods})"
  | _ => pure ()
  let emitShared := match part with | .range .. => false | _ => true

  let modPrefix := s!"LRATCatcher.Generated.{name}"
  let dir := s!"LRATCatcher/Generated/{name}"

  -- global number of chunk j is j; global number of parent rank r (0-based) is numChunks+r+1
  let parentGnum := fun (r : Nat) => numChunks + r + 1

  -- fail early on missing certificates for the parent modules we will emit
  for r in [0:numParents] do
    if part.emits (parentGnum r) then
      let i := parents[r]!
      unless (← System.FilePath.pathExists s!"{negsubDir}/leaf{i}_negsub.lrat") do
        die s!"sub-cover certificate not found: {negsubDir}/leaf{i}_negsub.lrat"
      unless (← System.FilePath.pathExists s!"{subicnfDir}/leaf{i}_d8.icnf") do
        die s!"subcube iCNF not found: {subicnfDir}/leaf{i}_d8.icnf"

  try IO.FS.createDirAll dir
  catch e => die s!"cannot create directory '{dir}': {e}"

  -- ============================ Base.lean ============================
  if emitShared then
    let h ← openOut s!"{dir}/Base.lean"
    h.putStr s!"import LRATCatcher.Cover\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    h.putStr s!"def base : CNF Nat := LRATCatcher.parseDimacs \"{escLean baseStr}\"\n\n"
    -- all top cubes
    for i in [1:n+1] do
      h.putStr s!"def cube{i} : Cube := {cubeLit cubes[i-1]!}\n"
    h.putStr "\n"
    -- per-chunk cube lists
    for j in [1:numChunks+1] do
      let arr := chunks[j-1]!
      let cs := String.intercalate ", " (arr.toList.map (fun i => s!"cube{i}"))
      h.putStr s!"def chunkCubes{j} : List Cube := [{cs}]\n"
    h.putStr "\n"
    -- per-parent: only the singleton parent-cube list. The subcube defs
    -- (`sub<i>_<k>`, `subs<i>`) live in Parent<i>.lean — they are used only
    -- there, and keeping them out of Base keeps Base small at scale (a
    -- Norin-class run would otherwise put ~2·10⁵ subcube defs here).
    for i in parents.toList do
      h.putStr s!"def parentCubes{i} : List Cube := [cube{i}]\n"
    h.putStr "\n"
    -- cubes = concatenation of segments in canonical order
    let segExprs := segOrder.toList.map (fun s => match s with
      | .inl j => s!"chunkCubes{j}"
      | .inr i => s!"parentCubes{i}")
    if segExprs.length ≤ segGroup then
      h.putStr s!"def cubes : List Cube := {String.intercalate " ++ " segExprs}\n\n"
    else
      let blocks := blocksOf segGroup segExprs
      for t in [1:blocks.length+1] do
        h.putStr s!"def cubesGrp{t} : List Cube := {String.intercalate " ++ " blocks[t-1]!}\n"
      let grpExprs := (List.range blocks.length).map (fun t => s!"cubesGrp{t+1}")
      h.putStr s!"\ndef cubes : List Cube := {String.intercalate " ++ " grpExprs}\n\n"
    h.putStr s!"end {modPrefix}\n"
    h.flush

  -- ============================ Chunk<j>.lean ============================
  for j in [1:numChunks+1] do
    if part.emits j then
      let arr := chunks[j-1]!
      let h ← openOut s!"{dir}/Chunk{j}.lean"
      h.putStr s!"import LRATCatcher.Generated.{name}.Base\nimport LRATCatcher.StreamOracle\n\n"
      h.putStr s!"open Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
      for i in arr.toList do
        h.putStr s!"lrat_stream_cnf leaf{i}_unsat (Cube.leafCNF cube{i} base) \"{escLean s!"{streamDir}/leaf{i}"}\"\n"
      h.putStr "\n"
      let proof := forallMemProof (arr.toList.map (fun i => s!"leaf{i}_unsat"))
      h.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
      h.putStr s!"theorem chunk{j}_ok : ∀ c ∈ chunkCubes{j}, (Cube.leafCNF c base).Unsat :=\n  {proof}\n\n"
      h.putStr s!"end {modPrefix}\n"
      h.flush

  -- ============================ Parent<i>.lean ============================
  for r in [0:numParents] do
    if part.emits (parentGnum r) then
      let i := parents[r]!
      let subCubes ← readSubCubes subicnfDir i
      let m := subCubes.size
      let negsub ← readInput s!"{negsubDir}/leaf{i}_negsub.lrat"
      let h ← openOut s!"{dir}/Parent{i}.lean"
      h.putStr s!"import LRATCatcher.Generated.{name}.Base\nimport LRATCatcher.StreamOracle\n\n"
      h.putStr s!"open Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
      -- subcube defs, local to this module (only Parent<i> uses them)
      for k in [1:m+1] do
        h.putStr s!"def sub{i}_{k} : Cube := {cubeLit subCubes[k-1]!}\n"
      let subsL := String.intercalate ", " ((List.range m).map (fun k => s!"sub{i}_{k+1}"))
      h.putStr s!"def subs{i} : List Cube := [{subsL}]\n\n"
      -- streamed subleaf refutations (parent-leaf-then-subunit order)
      for k in [1:m+1] do
        h.putStr s!"lrat_stream_cnf sub{i}_{k}_raw ((Cube.leafCNF cube{i} base) ++ (Cube.toCNF sub{i}_{k})) \"{escLean s!"{streamDir}/leaf{i}_{k}"}\"\n"
      h.putStr "\n"
      -- transfer to leafCNF form via unsat_append_comm
      for k in [1:m+1] do
        h.putStr s!"theorem sub{i}_{k}_ok : (Cube.leafCNF sub{i}_{k} (Cube.leafCNF cube{i} base)).Unsat :=\n  LRATCatcher.unsat_append_comm sub{i}_{k}_raw\n"
      h.putStr "\n"
      -- inner cover (embedded, small)
      h.putStr s!"set_option maxHeartbeats 0 in\n"
      h.putStr s!"theorem cover{i} : (negCubesCNF subs{i}).Unsat :=\n  LRATCatcher.checkLratCnf_sound _ \"{escLean negsub}\" (by native_decide)\n\n"
      -- inner composition → parent leaf UNSAT
      let subProof := forallMemProof ((List.range m).map (fun k => s!"sub{i}_{k+1}_ok"))
      h.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
      h.putStr s!"theorem parent{i}_unsat : (Cube.leafCNF cube{i} base).Unsat :=\n"
      h.putStr s!"  LRATCatcher.cover_unsat\n    ({subProof})\n    cover{i}\n\n"
      h.putStr s!"end {modPrefix}\n"
      h.flush

  if emitShared then
    -- ============================ Cover.lean ============================
    let coverStr ← readInput coverFile
    let h ← openOut s!"{dir}/Cover.lean"
    h.putStr s!"import LRATCatcher.Generated.{name}.Base\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    h.putStr s!"set_option maxHeartbeats 0 in\n"
    if relMode then
      h.putStr s!"theorem coverThm : (base ++ negCubesCNF cubes).Unsat :=\n  LRATCatcher.checkLratCnf_sound _ \"{escLean coverStr}\" (by native_decide)\n\n"
    else
      h.putStr s!"theorem coverThm : (negCubesCNF cubes).Unsat :=\n  LRATCatcher.checkLratCnf_sound _ \"{escLean coverStr}\" (by native_decide)\n\n"
    h.putStr s!"end {modPrefix}\n"
    h.flush

    -- ============================ Main.lean ============================
    let hm ← openOut s!"{dir}/Main.lean"
    hm.putStr s!"import LRATCatcher.Generated.{name}.Base\nimport LRATCatcher.Generated.{name}.Cover\n"
    for j in [1:numChunks+1] do
      hm.putStr s!"import LRATCatcher.Generated.{name}.Chunk{j}\n"
    for i in parents.toList do
      hm.putStr s!"import LRATCatcher.Generated.{name}.Parent{i}\n"
    hm.putStr s!"\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    -- comp : ∀ c ∈ cubes, (leafCNF c base).Unsat, via forall_mem_append over segments
    let segProofs := segOrder.toList.map (fun s => match s with
      | .inl j => s!"chunk{j}_ok"
      | .inr i => s!"(List.forall_mem_cons.mpr ⟨parent{i}_unsat, List.forall_mem_nil _⟩)")
    let m := segProofs.length
    let comp ←
      if m ≤ segGroup then
        pure (appendChain segProofs)
      else
        -- two-level grouping, mirroring the cubesGrp<t> structure in Base
        let blocks := blocksOf segGroup segProofs
        for t in [1:blocks.length+1] do
          hm.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
          hm.putStr s!"theorem grp{t}_ok : ∀ c ∈ cubesGrp{t}, (Cube.leafCNF c base).Unsat :=\n  {appendChain blocks[t-1]!}\n\n"
        pure (appendChain ((List.range blocks.length).map (fun t => s!"grp{t+1}_ok")))
    hm.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
    let coverLemma := if relMode then "cover_unsat_rel" else "cover_unsat"
    hm.putStr s!"theorem base_unsat : base.Unsat :=\n  LRATCatcher.{coverLemma}\n    ({comp})\n    coverThm\n\n"
    hm.putStr s!"#print axioms base_unsat\n\nend {modPrefix}\n"
    hm.flush

    -- ============================ streams.tsv ============================
    -- one line per stream: <ShortModule>\t<fifoPath>\t<archiveFile>, grouped by module.
    let hs ← openOut s!"{dir}/streams.tsv"
    for j in [1:numChunks+1] do
      for i in chunks[j-1]!.toList do
        hs.putStr s!"Chunk{j}\t{streamDir}/leaf{i}\tleaf{i}.lrat.zst\n"
    for i in parents.toList do
      let subCubes ← readSubCubes subicnfDir i
      for k in [1:subCubes.size+1] do
        hs.putStr s!"Parent{i}\t{streamDir}/leaf{i}_{k}\tleaf{i}_{k}.lrat.zst\n"
    hs.flush

    -- ============================ build.sh ============================
    let buildLines : List String :=
      ["#!/bin/bash",
       s!"# Build {modPrefix}.Main, retrying transient per-module build failures.",
       "# Run from the package root, AFTER driver.sh has built the streaming modules",
       "# (this final pass composes them + the cover; no streams needed here).",
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

    -- ============================ driver.sh ============================
    -- Feeds streaming modules from a compressed archive, in waves, then does the
    -- final composition build. Run from the package root.
    let driverLines : List String :=
      ["#!/bin/bash",
       s!"# Stream {modPrefix} certificates from a zstd archive and build.",
       "# Usage: bash " ++ dir ++ "/driver.sh ARCHIVE_DIR [WAVE_SIZE]   (run from package root)",
       "#   ARCHIVE_DIR holds leaf<i>.lrat.zst and leaf<i>_<k>.lrat.zst",
       "#   WAVE_SIZE modules are fed + built together (default 4; keep small locally).",
       "set -u",
       "ARCHIVE_DIR=\"${1:-}\"",
       "WAVE_SIZE=\"${2:-4}\"",
       "if [ -z \"$ARCHIVE_DIR\" ]; then echo \"usage: driver.sh ARCHIVE_DIR [WAVE_SIZE]\" 1>&2; exit 1; fi",
       s!"MANIFEST=\"{dir}/streams.tsv\"",
       s!"MODPREFIX=\"{modPrefix}\"",
       "if [ ! -f \"$MANIFEST\" ]; then echo \"driver.sh: missing $MANIFEST\" 1>&2; exit 1; fi",
       "# Base has no streams; build it first so streaming modules never rebuild it mid-stream.",
       "lake build \"$MODPREFIX.Base:olean\" || { echo \"driver.sh: Base build failed\" 1>&2; exit 1; }",
       "# ordered unique module short-names (portable read loop; mapfile is bash 4+)",
       "MODS=()",
       "while IFS= read -r m; do MODS+=(\"$m\"); done < <(cut -f1 \"$MANIFEST\" | awk '!seen[$0]++')",
       "",
       "build_wave() {",
       "  local -a wave=(\"$@\")",
       "  local -a fifos=() pids=() targets=()",
       "  local mod fifo arch",
       "  for mod in \"${wave[@]}\"; do",
       "    targets+=(\"$MODPREFIX.$mod:olean\")",
       "    while IFS=$'\\t' read -r fifo arch; do",
       "      mkdir -p \"$(dirname \"$fifo\")\"",
       "      rm -f \"$fifo\"; mkfifo \"$fifo\"",
       "      zstd -dc \"$ARCHIVE_DIR/$arch\" > \"$fifo\" &",
       "      pids+=(\"$!\"); fifos+=(\"$fifo\")",
       "    done < <(awk -F'\\t' -v M=\"$mod\" '$1==M{print $2\"\\t\"$3}' \"$MANIFEST\")",
       "  done",
       "  lake build \"${targets[@]}\"; local rc=$?",
       "  local p f",
       "  for p in \"${pids[@]}\"; do kill \"$p\" 2>/dev/null; wait \"$p\" 2>/dev/null; done",
       "  for f in \"${fifos[@]}\"; do rm -f \"$f\"; done",
       "  return $rc",
       "}",
       "",
       "i=0",
       "while [ \"$i\" -lt \"${#MODS[@]}\" ]; do",
       "  wave=(\"${MODS[@]:$i:$WAVE_SIZE}\")",
       "  echo \"driver.sh: wave [$i,$((i+${#wave[@]}))) : ${wave[*]}\"",
       "  if ! build_wave \"${wave[@]}\"; then",
       "    echo \"driver.sh: wave failed; retrying once\" 1>&2",
       "    build_wave \"${wave[@]}\" || { echo \"driver.sh: wave FAILED at index $i\" 1>&2; exit 1; }",
       "  fi",
       "  i=$((i+WAVE_SIZE))",
       "done",
       "# final composition (Cover + Main); streaming oleans are cached, no streams needed",
       s!"bash {dir}/build.sh"]
    writeOut s!"{dir}/driver.sh" (String.intercalate "\n" driverLines ++ "\n")

  match part with
  | .range lo hi =>
    IO.println s!"lratcatch-cover-stream: modules {lo}..{min hi totalMods} of {totalMods} (chunks 1..{numChunks}, parents {numChunks+1}..{totalMods}) in {dir}/"
  | _ =>
    IO.println s!"lratcatch-cover-stream: {n} top cubes ({numParents} re-cubed), {numChunks} chunk(s) + {numParents} parent(s) = {totalMods} module(s) in {dir}/"
    IO.println s!"  stream + build: bash {dir}/driver.sh ARCHIVE_DIR [WAVE_SIZE]   # from package root"
  return (0 : UInt32)
