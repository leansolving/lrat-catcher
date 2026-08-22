import LRATCatcher.Basic
import Std.Data.HashMap

/-!
# `lratcatch-compact-renumber` — renumber an LRAT certificate for compacting import

The compacting streaming checker (`checkStreamCnfC` / `lrat_stream_cnf_compact`)
compacts its clause database every `K` feed blocks: holes are dropped and live
clauses shift down to positions `1..live`. The certificate's ids and hints must
therefore be renumbered to those compacted positions. This tool performs that
renumbering **streaming**, line by line — it never holds more than the live-id
map in memory, so it handles certificates far larger than RAM (pipe through
`zstd` for archives).

The output is untrusted plumbing: the import re-checks every step, so a wrong
rewrite can only make the check fail, never make it succeed.

The tool mirrors the checker's state exactly:

* base clause `i` sits at position `i` (`1..nBase`; position 0 is the
  permanent `none` of the checker's array layout);
* each addition is pushed at the current end of the array — its printed id
  becomes that position, hints are remapped through the id→position map;
* a deletion frees its positions (ids remapped, then dropped from the map);
* after every `K · B` certificate lines (`B` = feed block size, default 4096 =
  the shim's `blockLines`; override both together via `--block` /
  `LRATCATCHER_STREAM_BLOCK`) the live positions are re-ranked in order —
  exactly the `compactSnapshot` the checker performs at that boundary.

Every input line yields exactly one output line (blocking is line-based, so
line counts must be preserved); unknown ids pass through unchanged (fail-safe:
the checker rejects them).

The base must contain no tautological (complementary-literal) and no
duplicate-literal clauses: the core converter silently drops clauses it cannot
represent, which would shift every base position (solver-facing CNFs are
normally clean). The tool refuses such bases.

Usage: `lratcatch-compact-renumber base.cnf in.lrat out.lrat K [--block B]`
(`in.lrat`/`out.lrat` may be `-` for stdin/stdout).
-/

open LRATCatcher

def die {α} (msg : String) : IO α := do
  IO.eprintln s!"lratcatch-compact-renumber: {msg}"
  IO.Process.exit 1

/-- Split a line into nonempty whitespace-separated tokens. -/
def tokensOf (line : String) : List String := Id.run do
  let mut out : List String := []
  for s in line.split (fun c => c == ' ' || c == '\t' || c == '\r') do
    let t := s.toString
    if !t.isEmpty then out := t :: out
  return out.reverse

structure St where
  posOf : Std.HashMap Nat Nat := {}   -- certificate id → current array position
  idAt : Std.HashMap Nat Nat := {}    -- current array position → certificate id
  nextPos : Nat := 0                  -- next push position (current array size)
  compactions : Nat := 0

/-- Re-rank the live positions in order — the tool-side mirror of
    `compactSnapshot` (position 0 stays the permanent hole). -/
def St.compact (st : St) : St := Id.run do
  let entries := (st.idAt.toArray.qsort (fun a b => a.1 < b.1))
  let mut posOf : Std.HashMap Nat Nat := {}
  let mut idAt : Std.HashMap Nat Nat := {}
  let mut r := 1
  for (_, id) in entries do
    posOf := posOf.insert id r
    idAt := idAt.insert r id
    r := r + 1
  return { posOf, idAt, nextPos := r, compactions := st.compactions + 1 }

/-- Rewrite one certificate line; identity on lines that are not LRAT actions.
    Returns the rewritten line and the updated state. -/
def rewriteLine (st : St) (line : String) : String × St := Id.run do
  let toks := tokensOf line
  match toks with
  | [] => return (line, st)
  | t0 :: rest =>
    if t0.toNat?.isNone then
      return (line, st)   -- comment or other non-action line: pass through
    match rest with
    | "d" :: ids =>
      -- deletion: remap each id to its position, free the slots
      let mut st := st
      let mut out : List String := ["d", t0]
      for tok in ids do
        match tok.toNat? with
        | some 0 => out := "0" :: out
        | some i =>
          match st.posOf.get? i with
          | some p =>
            st := { st with posOf := st.posOf.erase i, idAt := st.idAt.erase p }
            out := toString p :: out
          | none => out := tok :: out   -- unknown id: fail-safe pass-through
        | none => out := tok :: out
      return (String.intercalate " " out.reverse, st)
    | _ =>
      -- addition: dense new id = push position; clause verbatim; hints remapped
      let some origId := t0.toNat? | return (line, st)
      let newId := st.nextPos
      let mut out : List String := [toString newId]
      let mut inHints := false
      for tok in rest do
        if inHints then
          match tok.toInt? with
          | some 0 => out := "0" :: out
          | some h =>
            let a := h.natAbs
            let p := st.posOf.getD a a
            out := (if h < 0 then s!"-{p}" else toString p) :: out
          | none => out := tok :: out
        else
          out := tok :: out
          if tok == "0" then inHints := true
      let st := { st with
        posOf := st.posOf.insert origId newId
        idAt := st.idAt.insert newId origId
        nextPos := newId + 1 }
      return (String.intercalate " " out.reverse, st)

def main (args : List String) : IO UInt32 := do
  let usage := "usage: lratcatch-compact-renumber base.cnf in.lrat out.lrat K [--block B]   ('-' = stdin/stdout)"
  let (posArgs, blockB) ←
    match args.span (· != "--block") with
    | (pos, ["--block", b]) =>
      match b.toNat? with
      | some n => if n ≥ 1 then pure (pos, n) else die "--block must be ≥ 1"
      | none => die s!"bad --block '{b}'"
    | (pos, []) => pure (pos, 4096)
    | _ => die usage
  let (baseFile, inFile, outFile, kArg) ←
    match posArgs with
    | [b, i, o, k] => pure (b, i, o, k)
    | _ => die usage
  let some kBlocks := kArg.toNat? | die s!"K must be a number, got '{kArg}'"
  if kBlocks == 0 then die "K must be ≥ 1 (no compaction wanted? use plain lrat_stream_cnf)"

  -- base layout: positions 1..nBase; refuse bases the converter would thin out
  let baseStr ← try IO.FS.readFile baseFile
    catch e => die s!"cannot read '{baseFile}': {e}"
  let base := parseDimacs baseStr
  let nBase := base.clauses.size
  if nBase == 0 then die s!"no clauses parsed from '{baseFile}'"
  for i in [0:nBase] do
    let c := base.clauses[i]!
    let mut seen : Std.HashMap (Nat × Bool) Unit := {}
    for l in c do
      if seen.contains l then
        die s!"base clause {i+1} has a duplicate literal — base positions would shift (clean the CNF first)"
      if seen.contains (l.1, !l.2) then
        die s!"base clause {i+1} is a tautology — the checker drops it, shifting base positions (clean the CNF first)"
      seen := seen.insert l ()

  let inStream : IO.FS.Stream ←
    if inFile == "-" then IO.getStdin
    else IO.FS.Stream.ofHandle <$> (try IO.FS.Handle.mk inFile .read
      catch e => die s!"cannot read '{inFile}': {e}")
  let outStream : IO.FS.Stream ←
    if outFile == "-" then IO.getStdout
    else IO.FS.Stream.ofHandle <$> (try IO.FS.Handle.mk outFile .write
      catch e => die s!"cannot write '{outFile}': {e}")

  let mut st : St := {}
  for i in [1:nBase+1] do
    st := { st with posOf := st.posOf.insert i i, idAt := st.idAt.insert i i }
  st := { st with nextPos := nBase + 1 }

  let boundary := blockB * kBlocks
  let mut lines : Nat := 0
  let mut buf : String := ""
  repeat
    let line ← inStream.getLine
    if line.isEmpty then break
    let stripped := if line.back == '\n' then (line.dropEnd 1).toString else line
    let (out, st') := rewriteLine st stripped
    st := st'
    buf := buf ++ out ++ "\n"
    if buf.utf8ByteSize ≥ 1048576 then
      outStream.putStr buf
      buf := ""
    lines := lines + 1
    if lines % boundary == 0 then
      st := st.compact
  outStream.putStr buf
  outStream.flush
  IO.eprintln s!"lratcatch-compact-renumber: {lines} lines, {st.compactions} compaction(s), \
    {st.idAt.size} live clause(s) at end (base {nBase}, block {blockB}, K {kBlocks})"
  return 0
