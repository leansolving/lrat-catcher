import LRATLean.Cover

/-!
  # `lratlean-export` — generate solver input files for a cube-and-conquer run

  Usage: `lratlean-export base.cnf cubes.icnf outdir`

  Writes `outdir/leaf{i}.cnf` for each cube of the iCNF file (cube unit
  clauses first, then base — the clause order `lrat_cover_reflect` assumes
  for LRAT clause IDs), and `outdir/negcubes.cnf` (the cover-completeness
  CNF, to be refuted by the solver, producing `cover.lrat`).

  Files are printed with `Std.Sat.CNF.dimacs`, whose +1 variable shift inverts
  `LRATLean.parseDimacs`, so the Lean-side CNFs match the files byte-for-byte
  in clause structure.
-/

open Std.Sat

def main (args : List String) : IO UInt32 := do
  match args with
  | [baseFile, icnfFile, outDir] =>
    let baseStr ← IO.FS.readFile baseFile
    let icnfStr ← IO.FS.readFile icnfFile
    let base := LRATLean.parseDimacs baseStr
    let cubes := LRATLean.parseICnf icnfStr
    if cubes.isEmpty then
      IO.eprintln "lratlean-export: no cubes found in iCNF file"
      return 1
    IO.FS.createDirAll outDir
    let mut i := 1
    for c in cubes do
      let leaf := LRATLean.Cube.leafCNF c base
      unless LRATLean.dimacsRoundTrip leaf do
        IO.eprintln s!"lratlean-export: round-trip self-check failed for leaf {i}"
        return 1
      IO.FS.writeFile s!"{outDir}/leaf{i}.cnf" leaf.dimacs
      i := i + 1
    let negcubes := LRATLean.negCubesCNF cubes
    unless LRATLean.dimacsRoundTrip negcubes do
      IO.eprintln "lratlean-export: round-trip self-check failed for negcubes.cnf"
      return 1
    IO.FS.writeFile s!"{outDir}/negcubes.cnf" negcubes.dimacs
    IO.println s!"lratlean-export: wrote {cubes.length} leaf CNFs and negcubes.cnf to {outDir}"
    return 0
  | _ =>
    IO.eprintln "usage: lratlean-export base.cnf cubes.icnf outdir"
    return 1
