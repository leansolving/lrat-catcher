import LRATCatcher.Showcases.Ramsey
import LRATCatcher.Cover

/-!
  End-to-end Ramsey showcase: R(3,3) = 6, both bounds as statements about
  edge colorings (no CNF in the statements); plus the R(4,4) lower-bound
  witness (Paley graph of order 17).

  * Upper bound: `lratcatch-gen ramsey 6 3 3 examples/ramsey/r33_6.cnf`,
    refuted by `cadical --lrat --no-binary --no-factor`, imported by
    `ramsey_lrat` → `¬ hasRamseyFreeColoring 6 3 3`.
  * Lower bounds: explicit witness colorings checked by `native_decide`
    (pentagon C_5 for R(3,3) > 5; Paley(17) for R(4,4) > 17).
-/

namespace LRATCatcher.Tests

open LRATCatcher.Ramsey

-- Sanity: `edgeVar` enumerates the upper triangle bijectively (row-major).
-- Soundness does not need this, but the meaning of the statements does.
example : ((List.range 18).flatMap fun i => (List.range 18).filterMap fun j =>
    if i < j then some (edgeVar 18 i j) else none) = List.range 153 := by
  native_decide

-- Upper bound: every 2-coloring of K_6 has a monochromatic triangle.
ramsey_lrat r33_upper 6 3 3 "examples/ramsey/r33_6.lrat"

#print axioms r33_upper

-- Lower bound: the pentagon 2-coloring of K_5 (red = cycle edges).
def c5Coloring : Nat → Bool := fun v =>
  [edgeVar 5 0 1, edgeVar 5 1 2, edgeVar 5 2 3, edgeVar 5 3 4,
   edgeVar 5 0 4].contains v

theorem r33_lower : hasRamseyFreeColoring 5 3 3 :=
  witness_ramsey_free 5 3 3 c5Coloring (by native_decide)

/-- R(3,3) = 6, fully inside Lean. -/
theorem R33 : ramseyNumber 3 3 6 := ⟨r33_lower, r33_upper⟩

#print axioms R33

-- Cube-and-conquer rehearsal for the flagship: the same upper bound via a
-- 2-cube split, with the Lean-defined encoding as the certified base
-- (lrat_cover_reflect_cnf composed with the encoding soundness theorem).
lrat_cover_reflect_cnf r33_cnf_unsat_cc (LRATCatcher.Ramsey.encode 6 3 3)
  "examples/ramsey/r33cc/cubes.icnf" "examples/ramsey/r33cc/leaf"
  "examples/ramsey/r33cc/cover.lrat"

theorem r33_upper_cc : ¬hasRamseyFreeColoring 6 3 3 :=
  no_ramsey_free_of_unsat 6 3 3 r33_cnf_unsat_cc

#print axioms r33_upper_cc

-- R(4,4) lower bound: the Paley graph of order 17 — edge (i,j) red iff
-- j - i is a quadratic residue mod 17 — has no monochromatic K_4.
def qr17 : List Nat := [1, 2, 4, 8, 9, 13, 15, 16]

def paley17 : Nat → Bool := fun v =>
  (List.range 17).any fun i => (List.range 17).any fun j =>
    decide (i < j) && edgeVar 17 i j == v && qr17.contains (j - i)

theorem r44_lower : hasRamseyFreeColoring 17 4 4 :=
  witness_ramsey_free 17 4 4 paley17 (by native_decide)

#print axioms r44_lower

end LRATCatcher.Tests
