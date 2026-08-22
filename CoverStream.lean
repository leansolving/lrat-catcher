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

For live solve-and-import (no archive), `worker-live.sh` is emitted as a per-chunk
TEMPLATE: it starts the checker first (blocked on the first FIFO) and solves the
chunk's leaves one at a time, feeding each certificate into its FIFO and deleting it
immediately — at most two certificates on scratch at any moment. Do NOT replace this
with solve-everything-then-check glue: that multiplies per-task scratch by the chunk
size, and a job farm at full node packing can exhaust node-local scratch cluster-wide
even when every individual task fits.

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
  let usage := "usage: lratcatch-cover-stream base.cnf cubes.icnf cover.lrat recubed.txt subicnfdir negsubdir streamdir Name [K] [--part shared|LO:HI] [--rel] [--units-last] [--compact KC]\n  global module numbering: chunk modules 1..numChunks, then parent modules numChunks+1..\n  --rel: the top cover cert refutes base ++ negcubes (relative cover); composes via cover_unsat_rel\n  --units-last: leaf certs were solved from base-first DIMACS (cube units LAST); chunk statements stream (base ++ toCNF c) and transfer via unsat_append_comm\n  --compact KC: leaf checks compact their clause database every KC feed blocks (lrat_stream_cnf_compact); the archived certificates MUST be pre-renumbered with lratcatch-compact-renumber (same KC and block size)"
  let relMode := args.contains "--rel"
  let args := args.filter (· != "--rel")
  let unitsLast := args.contains "--units-last"
  let args := args.filter (· != "--units-last")
  let (args, compactK) ←
    match args.span (· != "--compact") with
    | (pre, "--compact" :: kc :: post) =>
      match kc.toNat? with
      | some n => if n ≥ 1 then pure (pre ++ post, some n)
                  else die "--compact must be ≥ 1"
      | none => die s!"bad --compact '{kc}'"
    | (pre, []) => pure (pre, none)
    | _ => die usage
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

  -- streaming command emitted for each leaf: plain, or compacting (--compact)
  let streamCmd := match compactK with
    | some kc => (s!"lrat_stream_cnf_compact", s!" {kc}")
    | none => ("lrat_stream_cnf", "")

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
  -- Deliberately tiny: only the base CNF and the canonical cube list, each a
  -- single string-literal def. Per-cube defs live in the module that uses
  -- them (Chunk<j>/Parent<i>): elaborating one `def cube<i> := [...]` costs
  -- ~15 ms and ~0.6 MB of elaborator RSS, so a run with
  -- ~3·10⁵ cubes in ONE module needs hours and ~200 GB (observed: 50K defs =
  -- 752 s / 32 GB), and every worker would load that olean. `cubes` is
  -- instead parsed from the embedded iCNF text; Main proves it equal to the
  -- concatenation of the per-module lists by `native_decide` (`cubes_eq`),
  -- which doubles as an end-to-end check of the chunk slicing.
  if emitShared then
    let h ← openOut s!"{dir}/Base.lean"
    h.putStr s!"import LRATCatcher.Cover\n\nopen Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
    h.putStr s!"def base : CNF Nat := LRATCatcher.parseDimacs \"{escLean baseStr}\"\n\n"
    h.putStr s!"def cubes : List Cube := LRATCatcher.parseICnf \"{escLean icnfStr}\"\n\n"
    h.putStr s!"end {modPrefix}\n"
    h.flush

  -- ============================ Chunk<j>.lean ============================
  for j in [1:numChunks+1] do
    if part.emits j then
      let arr := chunks[j-1]!
      let h ← openOut s!"{dir}/Chunk{j}.lean"
      h.putStr s!"import LRATCatcher.Generated.{name}.Base\nimport LRATCatcher.StreamOracle\n\n"
      h.putStr s!"open Std.Sat LRATCatcher\n\nnamespace {modPrefix}\n\n"
      -- this chunk's cube defs (kept out of Base — see the Base.lean comment)
      for i in arr.toList do
        h.putStr s!"def cube{i} : Cube := {cubeLit cubes[i-1]!}\n"
      let cs := String.intercalate ", " (arr.toList.map (fun i => s!"cube{i}"))
      h.putStr s!"def chunkCubes{j} : List Cube := [{cs}]\n\n"
      if unitsLast then
        -- leaves were solved from base-first DIMACS files (cube units LAST):
        -- the cert matches `base ++ toCNF c`; transfer to leafCNF form.
        for i in arr.toList do
          h.putStr s!"{streamCmd.1} leaf{i}_raw (base ++ Cube.toCNF cube{i}) \"{escLean s!"{streamDir}/leaf{i}"}\"{streamCmd.2}\n"
        h.putStr "\n"
        for i in arr.toList do
          h.putStr s!"theorem leaf{i}_unsat : (Cube.leafCNF cube{i} base).Unsat :=\n  LRATCatcher.unsat_append_comm leaf{i}_raw\n"
      else
        for i in arr.toList do
          h.putStr s!"{streamCmd.1} leaf{i}_unsat (Cube.leafCNF cube{i} base) \"{escLean s!"{streamDir}/leaf{i}"}\"{streamCmd.2}\n"
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
      -- this parent's top cube (kept out of Base — see the Base.lean comment)
      h.putStr s!"def cube{i} : Cube := {cubeLit cubes[i-1]!}\n"
      h.putStr s!"def parentCubes{i} : List Cube := [cube{i}]\n\n"
      -- subcube defs, local to this module (only Parent<i> uses them)
      for k in [1:m+1] do
        h.putStr s!"def sub{i}_{k} : Cube := {cubeLit subCubes[k-1]!}\n"
      let subsL := String.intercalate ", " ((List.range m).map (fun k => s!"sub{i}_{k+1}"))
      h.putStr s!"def subs{i} : List Cube := [{subsL}]\n\n"
      -- streamed subleaf refutations (parent-leaf-then-subunit order)
      for k in [1:m+1] do
        h.putStr s!"{streamCmd.1} sub{i}_{k}_raw ((Cube.leafCNF cube{i} base) ++ (Cube.toCNF sub{i}_{k})) \"{escLean s!"{streamDir}/leaf{i}_{k}"}\"{streamCmd.2}\n"
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
    -- The canonical `cubes` (Base) is PARSED from the iCNF text; the segment
    -- lists live in the chunk/parent modules. Reconnect them here: grouped
    -- append defs (≤ segGroup wide at both levels, against elaborator stack
    -- overflow), one `native_decide` identity `cubes_eq`, and the
    -- forall_mem_append composition transported along it.
    let segExprs := segOrder.toList.map (fun s => match s with
      | .inl j => s!"chunkCubes{j}"
      | .inr i => s!"parentCubes{i}")
    let exprBlocks := blocksOf segGroup segExprs
    for t in [1:exprBlocks.length+1] do
      hm.putStr s!"def cubesGrp{t} : List Cube := {String.intercalate " ++ " exprBlocks[t-1]!}\n"
    let grouped := String.intercalate " ++ " ((List.range exprBlocks.length).map (fun t => s!"cubesGrp{t+1}"))
    hm.putStr s!"\nset_option maxHeartbeats 0 in\ntheorem cubes_eq : cubes = {grouped} := by native_decide\n\n"
    let segProofs := segOrder.toList.map (fun s => match s with
      | .inl j => s!"chunk{j}_ok"
      | .inr i => s!"(List.forall_mem_cons.mpr ⟨parent{i}_unsat, List.forall_mem_nil _⟩)")
    let proofBlocks := blocksOf segGroup segProofs
    for t in [1:proofBlocks.length+1] do
      hm.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
      hm.putStr s!"theorem grp{t}_ok : ∀ c ∈ cubesGrp{t}, (Cube.leafCNF c base).Unsat :=\n  {appendChain proofBlocks[t-1]!}\n\n"
    let comp := appendChain ((List.range proofBlocks.length).map (fun t => s!"grp{t+1}_ok"))
    hm.putStr s!"set_option maxHeartbeats 0 in\nset_option maxRecDepth 1000000 in\n"
    let coverLemma := if relMode then "cover_unsat_rel" else "cover_unsat"
    hm.putStr s!"theorem base_unsat : base.Unsat :=\n  LRATCatcher.{coverLemma}\n    (fun c hc => ({comp}) c (cubes_eq ▸ hc))\n    coverThm\n\n"
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
       "ulimit -s unlimited 2>/dev/null || true",
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

    -- ============================ worker-live.sh ============================
    -- Pipelined live-solve worker TEMPLATE (per chunk module): the checker is
    -- started FIRST (it blocks on the first FIFO), then leaves are solved one
    -- at a time and each certificate is cat-ed into its FIFO and deleted —
    -- at most two certificates on scratch at any moment. The alternative
    -- (solve everything, then check) multiplies per-task scratch by the chunk
    -- size, and a farm at full node packing can exhaust node-local scratch
    -- cluster-wide even though every single task fits comfortably.
    let workerLines : List String :=
      ["#!/bin/bash",
       s!"# Pipelined live-solve worker TEMPLATE for {modPrefix} chunk modules.",
       "# Usage: worker-live.sh <chunk-number>   (run from the package root;",
       "# build the Base module first: lake build " ++ modPrefix ++ ".Base:olean).",
       "# EDIT the CONFIG block before use. Exit codes: 0 ok, 2 check failed,",
       "# 3 a leaf was SAT (falsifies the cover — investigate!), 99 requeue",
       "# (infrastructure: low disk, solver crash, timeout; SGE requeues on",
       "# 'qsub -r y' when the script exits 99).",
       "set -u",
       "ulimit -s unlimited 2>/dev/null || true",
       "",
       "# ---- CONFIG (edit) ----",
       s!"BASE=\"{escLean baseFile}\"          # base DIMACS (as passed to the generator)",
       s!"CUBES=\"{escLean icnfFile}\"         # iCNF cube file ('a ... 0' lines)",
       "SOLVER=\"cadical\"",
       "SOLVER_FLAGS=\"--lrat --no-factor\"   # binary LRAT is fine (feed auto-detects)",
       "TIMEOUT_SOLVE=43200",
       "TIMEOUT_FEED=7200",
       "MIN_FREE_G=8                        # requeue if scratch has less than this",
       s!"K={kChunk}                              # leaves per chunk (generator K)",
       "TOOLROOT=\"$PWD\"                     # package root (resolve symlinks for lean -R)",
       "SCRATCH=\"${TMPDIR:-/tmp}\"",
       "# -----------------------",
       "",
       "J=\"${1:?usage: worker-live.sh <chunk-number>}\"",
       s!"MOD=\"{modPrefix}.Chunk$J\"",
       s!"SRC=\"{dir}/Chunk$J.lean\"",
       s!"MANIFEST=\"{dir}/streams.tsv\"",
       "TC=$(dirname \"$(dirname \"$(command -v lean)\")\")",
       "export LEAN_PATH=\"$TOOLROOT/.lake/build/lib/lean:$TC/lib/lean\"",
       "export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}",
       "",
       "# scratch guard: a full scratch disk fails every solve with confusing rc",
       "FREE_G=$(df -P \"$SCRATCH\" | awk 'NR==2{print int($4/1048576)}')",
       "if [ \"${FREE_G:-0}\" -lt \"$MIN_FREE_G\" ]; then echo \"low scratch (${FREE_G}G) — requeue\" 1>&2; exit 99; fi",
       "",
       "# this chunk's FIFOs, in leaf order, from the manifest",
       "FIFOS=()",
       "while IFS= read -r f; do FIFOS+=(\"$f\"); done < <(awk -F'\\t' -v M=\"Chunk$J\" '$1==M{print $2}' \"$MANIFEST\")",
       "[ \"${#FIFOS[@]}\" -gt 0 ] || { echo \"no streams for Chunk$J in $MANIFEST\" 1>&2; exit 99; }",
       "for f in \"${FIFOS[@]}\"; do mkdir -p \"$(dirname \"$f\")\"; rm -f \"$f\"; mkfifo \"$f\"; done",
       "cleanup () { for f in \"${FIFOS[@]}\"; do rm -f \"$f\"; done; }",
       "",
       "# start the checker FIRST — it blocks reading the first FIFO",
       "( lean -R \"$TOOLROOT\" \"$SRC\" -o \"$SCRATCH/Chunk$J.olean\" > \"$SCRATCH/lean$J.out\" 2>&1; echo $? > \"$SCRATCH/lean$J.rc\" ) &",
       "LEANPID=$!",
       "",
       "# leaf indices of this chunk: FIFO basenames are leaf<i>",
       "fail=0",
       "for f in \"${FIFOS[@]}\"; do",
       "  i=$(basename \"$f\" | sed 's/[^0-9]*//')",
       "  # leaf CNF: cube units FIRST, then base clauses (leafCNF c base =",
       "  # c.toCNF ++ base; LRAT ids are positional). With --units-last",
       "  # generation, put the base clauses first and the units last instead.",
       "  LITS=$(awk -v n=\"$i\" '/^a /{c++; if (c==n) {sub(/^a /,\"\"); sub(/ 0$/,\"\"); print; exit}}' \"$CUBES\")",
       "  NL=$(echo \"$LITS\" | wc -w)",
       "  read -r NV NC < <(awk '/^p cnf/{print $3, $4; exit}' \"$BASE\")",
       "  { echo \"p cnf $NV $((NC+NL))\"; for l in $LITS; do echo \"$l 0\"; done; grep -v '^p cnf' \"$BASE\"; } > \"$SCRATCH/leaf$i.cnf\"",
       "  timeout \"$TIMEOUT_SOLVE\" $SOLVER $SOLVER_FLAGS \"$SCRATCH/leaf$i.cnf\" \"$SCRATCH/cert$i.lrat\" > \"$SCRATCH/solve$i.log\" 2>&1",
       "  rc=$?",
       "  if [ $rc -eq 10 ]; then fail=3; break; fi",
       "  if [ $rc -ne 20 ] || [ ! -s \"$SCRATCH/cert$i.lrat\" ]; then fail=99; break; fi",
       "  kill -0 $LEANPID 2>/dev/null || { fail=99; break; }",
       "  # feed the checker (blocks until consumed = backpressure), then drop the cert",
       "  timeout \"$TIMEOUT_FEED\" cat \"$SCRATCH/cert$i.lrat\" > \"$f\" || { fail=99; break; }",
       "  rm -f \"$SCRATCH/cert$i.lrat\" \"$SCRATCH/leaf$i.cnf\" \"$SCRATCH/solve$i.log\"",
       "done",
       "",
       "if [ $fail -ne 0 ]; then",
       "  kill $LEANPID 2>/dev/null; wait $LEANPID 2>/dev/null; cleanup",
       "  [ $fail -eq 3 ] && echo \"leaf $i is SAT — the cover is falsified, do NOT requeue\" 1>&2",
       "  exit $fail",
       "fi",
       "wait $LEANPID 2>/dev/null",
       "rc=$(cat \"$SCRATCH/lean$J.rc\" 2>/dev/null || echo 900)",
       "cleanup",
       "if [ \"$rc\" = \"0\" ] && [ -s \"$SCRATCH/Chunk$J.olean\" ]; then",
       "  DEST=\"$TOOLROOT/.lake/build/lib/lean/$(echo \"" ++ modPrefix ++ "\" | tr '.' '/')\"",
       "  mkdir -p \"$DEST\"",
       "  cp \"$SCRATCH/Chunk$J.olean\" \"$DEST/.C$J.$$\" && mv \"$DEST/.C$J.$$\" \"$DEST/Chunk$J.olean\"",
       "  exit 0",
       "else",
       "  head -30 \"$SCRATCH/lean$J.out\" 1>&2",
       "  exit 2",
       "fi"]
    writeOut s!"{dir}/worker-live.sh" (String.intercalate "\n" workerLines ++ "\n")

  match part with
  | .range lo hi =>
    IO.println s!"lratcatch-cover-stream: modules {lo}..{min hi totalMods} of {totalMods} (chunks 1..{numChunks}, parents {numChunks+1}..{totalMods}) in {dir}/"
  | _ =>
    IO.println s!"lratcatch-cover-stream: {n} top cubes ({numParents} re-cubed), {numChunks} chunk(s) + {numParents} parent(s) = {totalMods} module(s) in {dir}/"
    IO.println s!"  stream + build: bash {dir}/driver.sh ARCHIVE_DIR [WAVE_SIZE]   # from package root"
    if let some kc := compactK then
      IO.println s!"  --compact {kc}: archive certificates MUST be pre-renumbered (lratcatch-compact-renumber base K={kc}, matching block size)"
  return (0 : UInt32)
