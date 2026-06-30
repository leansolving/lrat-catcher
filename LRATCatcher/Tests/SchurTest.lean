import LRATCatcher.Showcases.Schur

/-!
  End-to-end Schur showcase: S(3) = 13, both bounds as statements about
  colorings (no CNF in the statements).

  * Upper bound: `lratcatch-gen schur 3 14 examples/schur/schur_3_14.cnf`,
    refuted by `cadical --lrat --no-binary --no-factor`, imported by
    `schur_lrat` → `¬ hasKSchurFreeColoring 3 14`.
  * Lower bound: explicit witness partition {1,4,10,13} | {2,3,11,12} |
    {5,…,9}, checked by `native_decide`.
-/

namespace LRATCatcher.Tests

open LRATCatcher.Schur

-- Upper bound: no Schur-free 3-coloring of {1,…,14}.
schur_lrat schur3_upper 3 14 "examples/schur/schur_3_14.lrat"

#print axioms schur3_upper

-- Lower bound witness coloring of {1,…,13}.
def schurWitness3 : Nat → Nat := fun i =>
  if i ∈ [1, 4, 10, 13] then 0 else if i ∈ [2, 3, 11, 12] then 1 else 2

theorem schur3_lower : hasKSchurFreeColoring 3 13 :=
  witness_k_schur_free 3 13 schurWitness3 (by native_decide)

#print axioms schur3_lower

/-- S(3) = 13, fully inside Lean. -/
theorem S3 : schurNumber 3 13 := ⟨schur3_lower, schur3_upper⟩

#print axioms S3

-- S(4) lower-bound witness coloring of {1,…,44} (found by cadical on the
-- SAT instance `lratcatch-gen schur 4 44`, re-verified by `native_decide`;
-- the matching upper bound ¬hasKSchurFreeColoring 4 45, giving S(4)=44, comes
-- from a cube-and-conquer refutation of `encodeK 4 45` that is too large to ship
-- here).
def schurWitness4 : Nat → Nat := fun i =>
  if i ∈ [8, 17, 18, 21, 22, 24, 27, 28, 31, 37] then 0
  else if i ∈ [2, 6, 7, 10, 11, 15, 34, 35, 38, 39, 43] then 1
  else if i ∈ [3, 4, 13, 14, 20, 25, 30, 32, 41, 42] then 2
  else 3

theorem schur4_lower : hasKSchurFreeColoring 4 44 :=
  witness_k_schur_free 4 44 schurWitness4 (by native_decide)

#print axioms schur4_lower

end LRATCatcher.Tests
