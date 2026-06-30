import LRATCatcher.Showcases.Schur
import LRATCatcher.Showcases.Ramsey

/-!
  # `lratcatch-gen` — generate solver input files for showcase encodings

  Usage:
  * `lratcatch-gen schur k n out.cnf`
  * `lratcatch-gen ramsey n s t out.cnf`

  Writes the DIMACS encoding of "`{1,…,n}` has a Schur-free k-coloring"
  (resp. "`K_n` has a 2-coloring with no red `K_s` and no blue `K_t`"),
  produced from the *same* encoding function (`LRATCatcher.Schur.encodeK`,
  `LRATCatcher.Ramsey.encode`) the `schur_lrat` / `ramsey_lrat` commands certify
  against, so the solved CNF and the certified CNF coincide by construction.
  Printed with `Std.Sat.CNF.dimacs` (+1 variable shift, inverse of
  `LRATCatcher.parseDimacs`).
-/

open Std.Sat

/-- Write a file, exiting cleanly if the path is not writable. -/
def writeOutput (path content : String) : IO Unit := do
  try
    IO.FS.writeFile path content
  catch e =>
    IO.eprintln s!"lratcatch-gen: cannot write '{path}': {e}"
    IO.Process.exit 1

def usage : String :=
  "usage: lratcatch-gen schur k n out.cnf | lratcatch-gen ramsey n s t out.cnf"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["schur", kStr, nStr, outFile] =>
    match kStr.toNat?, nStr.toNat? with
    | some k, some n =>
      if k == 0 then
        IO.eprintln "lratcatch-gen: k must be positive"
        return 1
      let cnf := LRATCatcher.Schur.encodeK k n
      unless LRATCatcher.dimacsRoundTrip cnf do
        IO.eprintln "lratcatch-gen: round-trip self-check failed"
        return 1
      writeOutput outFile cnf.dimacs
      IO.println s!"lratcatch-gen: wrote encodeK {k} {n} to {outFile}"
      return 0
    | _, _ =>
      IO.eprintln "lratcatch-gen: k and n must be numbers"
      return 1
  | ["ramsey", nStr, sStr, tStr, outFile] =>
    match nStr.toNat?, sStr.toNat?, tStr.toNat? with
    | some n, some s, some t =>
      let cnf := LRATCatcher.Ramsey.encode n s t
      unless LRATCatcher.dimacsRoundTrip cnf do
        IO.eprintln "lratcatch-gen: round-trip self-check failed"
        return 1
      writeOutput outFile cnf.dimacs
      IO.println s!"lratcatch-gen: wrote Ramsey encode {n} {s} {t} to {outFile}"
      return 0
    | _, _, _ =>
      IO.eprintln "lratcatch-gen: n, s, t must be numbers"
      return 1
  | _ =>
    IO.eprintln usage
    return 1
