import LRATCatcher.Basic
import Std.Tactic.BVDecide.LRAT

/-!
  # lratcatch-normalize — renumber an LRAT certificate to dense ids

  `drat-trim -L` (and other converters that keep the original DRAT clause
  numbering while emitting only core lemmas) produce LRAT files whose
  addition ids have GAPS. The Lean core checker ignores the declared ids and
  appends additions densely after the base clauses, so hints and deletions
  that refer to the original (gapped) numbering point at the wrong clause
  positions and the check fails — on a perfectly valid certificate.

  This tool rewrites such a certificate to the dense numbering the checker
  expects:

  * addition ids are reassigned densely from `nBase + 1` (the checker
    ignores them anyway, but the printed file is then also human-consistent);
  * every hint id `> nBase` is remapped through the original→dense table
    (ids `≤ nBase` are base-clause positions and pass through unchanged;
    a hint referring to a lemma that never appeared is left as-is — the
    checker will then reject the certificate, which is the correct fail-safe
    behavior for a genuinely broken file);
  * deletions of ids that were never added (drat-trim's skipped lemmas) are
    dropped; remaining deletion ids are remapped.

  The output is untrusted plumbing: a wrong rewrite can only make the
  checker reject, never accept an invalid certificate.

  Usage: `lratcatch-normalize base.cnf in.lrat out.lrat`

  The whole certificate is parsed in memory — intended for offline
  conversion, not for streaming-scale inputs (chunk first if needed).

  Assumes the converter numbered additions strictly above the base-clause
  count (true for drat-trim, whose DRAT numbering starts at nClauses+1); an
  addition id `≤ nBase` would shadow a base position and is reported.
-/

open Std.Tactic.BVDecide.LRAT (IntAction parseLRATProof)

namespace LRATCatcher.Normalize

/-- Remap one hint id: base positions pass through, lemma ids go through the
    table, unknown ids stay (fail-safe: the checker rejects them). -/
@[inline] def remapHint (nBase : Nat) (map : Std.HashMap Nat Nat) (h : Nat) : Nat :=
  if h ≤ nBase then h else map.getD h h

/-- Renumber additions densely from `nBase + 1`, remap hints, drop deletions
    of never-added ids. Returns the rewritten actions plus the number of
    dropped deletion ids and of suspicious low addition ids (`≤ nBase`). -/
def renumber (nBase : Nat) (acts : Array IntAction) :
    Array IntAction × Nat × Nat := Id.run do
  let mut map : Std.HashMap Nat Nat := {}
  let mut next := nBase + 1
  let mut out : Array IntAction := #[]
  let mut droppedDels := 0
  let mut lowIds := 0
  for a in acts do
    match a with
    | .addEmpty id hints =>
      if id ≤ nBase then lowIds := lowIds + 1
      out := out.push (.addEmpty next (hints.map (remapHint nBase map)))
      map := map.insert id next
      next := next + 1
    | .addRup id c hints =>
      if id ≤ nBase then lowIds := lowIds + 1
      out := out.push (.addRup next c (hints.map (remapHint nBase map)))
      map := map.insert id next
      next := next + 1
    | .addRat id c p rup rat =>
      if id ≤ nBase then lowIds := lowIds + 1
      let rat' := rat.map fun (rid, hs) =>
        (remapHint nBase map rid, hs.map (remapHint nBase map))
      out := out.push (.addRat next c p (rup.map (remapHint nBase map)) rat')
      map := map.insert id next
      next := next + 1
    | .del ids =>
      let ids' := ids.filterMap fun i =>
        if i ≤ nBase then some i else map.get? i
      droppedDels := droppedDels + (ids.size - ids'.size)
      if !ids'.isEmpty then
        out := out.push (.del ids')
  return (out, droppedDels, lowIds)

/-- Print one action in ASCII LRAT syntax. `cur` is the id used for deletion
    lines (the last assigned addition id, or `nBase` before any addition). -/
def printAction (cur : Nat) : IntAction → String
  | .addEmpty id hints =>
    String.intercalate " "
      ([toString id, "0"] ++ hints.toList.map toString ++ ["0"])
  | .addRup id c hints =>
    String.intercalate " "
      ([toString id] ++ c.toList.map toString ++ ["0"] ++
       hints.toList.map toString ++ ["0"])
  | .addRat id c _ rup rat =>
    -- the pivot is the first literal of `c` by LRAT convention (the parser
    -- derived it from there, so printing `c` reproduces it)
    let ratS := rat.toList.flatMap fun (rid, hs) =>
      s!"-{rid}" :: hs.toList.map toString
    String.intercalate " "
      ([toString id] ++ c.toList.map toString ++ ["0"] ++
       rup.toList.map toString ++ ratS ++ ["0"])
  | .del ids =>
    String.intercalate " "
      ([toString cur, "d"] ++ ids.toList.map toString ++ ["0"])

/-- Current id after an action (for deletion-line prefixes). -/
def idOf (cur : Nat) : IntAction → Nat
  | .addEmpty id _ | .addRup id _ _ | .addRat id _ _ _ _ => id
  | .del _ => cur

end LRATCatcher.Normalize

open LRATCatcher LRATCatcher.Normalize in
def main (args : List String) : IO UInt32 := do
  let [baseFile, inFile, outFile] := args
    | IO.eprintln "usage: lratcatch-normalize base.cnf in.lrat out.lrat"
      return 1
  let baseStr ← IO.FS.readFile baseFile
  let nBase := (parseDimacs baseStr).clauses.size
  if nBase == 0 then
    IO.eprintln s!"error: no clauses parsed from '{baseFile}'"
    return 1
  let certBytes ← IO.FS.readBinFile inFile
  let acts ← match parseLRATProof certBytes with
    | .ok a => pure a
    | .error e =>
      IO.eprintln s!"error: cannot parse '{inFile}': {e}"
      return 1
  let (out, droppedDels, lowIds) := renumber nBase acts
  let h ← IO.FS.Handle.mk outFile .write
  let mut cur := nBase
  for a in out do
    h.putStrLn (printAction cur a)
    cur := idOf cur a
  h.flush
  IO.println s!"lratcatch-normalize: {acts.size} actions in, {out.size} out \
    (base {nBase} clauses, {droppedDels} deletion ids of never-added lemmas dropped)"
  if lowIds > 0 then
    IO.eprintln s!"warning: {lowIds} addition ids were ≤ base clause count — \
      input numbering overlaps base positions; hints touching them may be wrong"
  return 0
