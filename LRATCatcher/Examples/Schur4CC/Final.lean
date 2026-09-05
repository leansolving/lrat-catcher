import LRATCatcher.Examples.Schur4CC.Main

/-!
  # S(4) = 44, by cube-and-conquer with streamed certificates

  The generated modules next to this file (`Base`, `Chunk1`, `Cover`, `Main`;
  produced by `examples/schur4cc/run.sh`) prove `base.Unsat` for
  `base := LRATCatcher.Schur.encodeK 4 45`, the Lean encoding of "a Schur-free
  4-colouring of {1,…,45} exists": eight leaf refutations, each checked as its
  certificate streams from `examples/schur4cc/leaves/leaf<i>`, plus the embedded
  cover certificate, composed by the proved lemma `cover_unsat`.

  This module adds the two steps that turn a CNF statement into a statement
  about colourings: encoding soundness (`no_k_schur_free_of_unsat`) for the
  upper bound, and a checked witness colouring of {1,…,44} for the lower bound.
-/

namespace LRATCatcher.Examples.Schur4CC

open LRATCatcher.Schur

/-- Upper bound: no Schur-free 4-colouring of {1,…,45}. -/
theorem schur4_upper : ¬hasKSchurFreeColoring 4 45 :=
  no_k_schur_free_of_unsat 4 45 (by omega) base_unsat

/-- Lower-bound witness: a Schur-free 4-colouring of {1,…,44} (found by cadical
    on the satisfiable instance `lratcatch-gen schur 4 44`). -/
def schurWitness4 : Nat → Nat := fun i =>
  if i ∈ [8, 17, 18, 21, 22, 24, 27, 28, 31, 37] then 0
  else if i ∈ [2, 6, 7, 10, 11, 15, 34, 35, 38, 39, 43] then 1
  else if i ∈ [3, 4, 13, 14, 20, 25, 30, 32, 41, 42] then 2
  else 3

theorem schur4_lower : hasKSchurFreeColoring 4 44 :=
  witness_k_schur_free 4 44 schurWitness4 (by native_decide)

/-- S(4) = 44: {1,…,44} admits a Schur-free 4-colouring and {1,…,45} does not. -/
theorem S4 : schurNumber 4 44 := ⟨schur4_lower, schur4_upper⟩

#print axioms S4

end LRATCatcher.Examples.Schur4CC
