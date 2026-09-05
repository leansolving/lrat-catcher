import LRATCatcher.StreamOracle

/-!
  # LRATCatcher.StreamFeedIrrel — the streaming checker reads a finite window

  A streamed import gets its certificate from an oracle `feed : Nat → Option
  (Array IntAction)` whose value no proof can inspect, so it is fair to ask
  *how much* of that oracle a completed check actually depends on. The answer
  is: a finite, explicitly bounded prefix. A run started at block index `i`
  with fuel `fuel` consults the feed only at indices in the window
  `[i, i + fuel)` — it reads block `i`, and recurses at `i + 1` with one unit
  of fuel less — so any two feeds that agree on that window produce literally
  the same verdict. Consequently the `native_decide` axiom recorded for a
  streamed theorem pins the oracle at finitely many indices, and the theorem
  it certifies holds for every feed extending those blocks; nothing outside
  the window can affect the outcome. The same holds for the compacting
  variant `checkStreamC`, whose extra state transformation does not touch
  the feed.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher

/-! ## The plain streaming checker -/

/-- **Feed irrelevance outside the window.** `checkStream feed f fuel i`
    depends on `feed` only at the indices `i, i+1, …, i+fuel-1`. -/
theorem checkStream_feed_agree {n : Nat} (feed feed' : Nat → Option (Array IntAction))
    (fuel : Nat) :
    ∀ (f : DefaultFormula n) (i : Nat),
      (∀ k, i ≤ k → k < i + fuel → feed k = feed' k) →
      checkStream feed f fuel i = checkStream feed' f fuel i := by
  induction fuel with
  | zero => intro f i _; rfl
  | succ fuel ih =>
    intro f i hagree
    rw [checkStream, checkStream]
    have h0 : feed i = feed' i := hagree i (Nat.le_refl i) (by omega)
    rw [h0]
    cases hfeed : feed' i with
    | none => rfl
    | some chunk =>
      simp only
      cases hrun : runChunk f chunk 0 with
      | none => rfl
      | some out =>
        cases out with
        | refuted => rfl
        | more f' =>
          simp only
          exact ih f' (i + 1) (fun k hk1 hk2 => hagree k (by omega) (by omega))

/-- Entry-point form: the verdict of `checkStreamCnf` is determined by the
    blocks `feed 0, …, feed (fuel-1)`. -/
theorem checkStreamCnf_feed_agree (cnf : CNF Nat)
    (feed feed' : Nat → Option (Array IntAction)) (fuel : Nat)
    (h : ∀ k, k < fuel → feed k = feed' k) :
    checkStreamCnf cnf feed fuel = checkStreamCnf cnf feed' fuel :=
  checkStream_feed_agree feed feed' fuel (CNF.convertLRAT cnf) 0
    (fun k _ hk => h k (by omega))

/-- **The corollary the paper argument uses.** If a streamed import accepts
    under `feed`, then it accepts — and hence proves the same CNF unsatisfiable
    — under *every* feed agreeing with `feed` on the finitely many blocks
    `0, …, fuel-1`. -/
theorem checkStreamCnf_true_of_agree (cnf : CNF Nat)
    (feed feed' : Nat → Option (Array IntAction)) (fuel : Nat)
    (h : ∀ k, k < fuel → feed k = feed' k)
    (hacc : checkStreamCnf cnf feed fuel = true) :
    checkStreamCnf cnf feed' fuel = true :=
  (checkStreamCnf_feed_agree cnf feed feed' fuel h) ▸ hacc

/-! ## The compacting streaming checker -/

/-- Feed irrelevance for the compacting variant: compaction rewrites the
    state between blocks but never consults the feed, so the window is the
    same `[i, i + fuel)`. -/
theorem checkStreamC_feed_agree {n : Nat} (feed feed' : Nat → Option (Array IntAction))
    (k : Nat) (fuel : Nat) :
    ∀ (f : DefaultFormula n) (i : Nat),
      (∀ j, i ≤ j → j < i + fuel → feed j = feed' j) →
      checkStreamC feed k f fuel i = checkStreamC feed' k f fuel i := by
  induction fuel with
  | zero => intro f i _; rfl
  | succ fuel ih =>
    intro f i hagree
    rw [checkStreamC, checkStreamC]
    have h0 : feed i = feed' i := hagree i (Nat.le_refl i) (by omega)
    rw [h0]
    cases hfeed : feed' i with
    | none => rfl
    | some chunk =>
      simp only
      cases hrun : runChunk f chunk 0 with
      | none => rfl
      | some out =>
        cases out with
        | refuted => rfl
        | more f' =>
          simp only
          exact ih (compactEvery k (i + 1) f') (i + 1)
            (fun j hj1 hj2 => hagree j (by omega) (by omega))

theorem checkStreamCnfC_feed_agree (cnf : CNF Nat)
    (feed feed' : Nat → Option (Array IntAction)) (fuel k : Nat)
    (h : ∀ j, j < fuel → feed j = feed' j) :
    checkStreamCnfC cnf feed fuel k = checkStreamCnfC cnf feed' fuel k :=
  checkStreamC_feed_agree feed feed' k fuel (CNF.convertLRAT cnf) 0
    (fun j _ hj => h j (by omega))

theorem checkStreamCnfC_true_of_agree (cnf : CNF Nat)
    (feed feed' : Nat → Option (Array IntAction)) (fuel k : Nat)
    (h : ∀ j, j < fuel → feed j = feed' j)
    (hacc : checkStreamCnfC cnf feed fuel k = true) :
    checkStreamCnfC cnf feed' fuel k = true :=
  (checkStreamCnfC_feed_agree cnf feed feed' fuel k h) ▸ hacc

#print axioms checkStream_feed_agree
#print axioms checkStreamCnf_feed_agree
#print axioms checkStreamCnf_true_of_agree
#print axioms checkStreamC_feed_agree
#print axioms checkStreamCnfC_feed_agree
#print axioms checkStreamCnfC_true_of_agree

end LRATCatcher
