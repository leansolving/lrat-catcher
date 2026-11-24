import Std.Tactic.BVDecide.LRAT

/-!
  # LRATCatcher.Kernel — kernel-mode LRAT checking (zero compiler trust)

  A variant of the LRAT check whose Boolean evaluation reduces inside the
  Lean *kernel* (`decide +kernel`), so the compiled evaluator (`native_decide`)
  is not part of the trust base.

  The checker works on the clause database of the core checker
  (`Std.Tactic.BVDecide.LRAT.Internal.State`) and reuses its public pieces
  that reduce in the kernel: `State.add`, `State.deleteMany`, `State.get?`,
  `State.toCNF` and their lemmas. The core RUP and RAT checks do not reduce in
  the kernel: their partial assignment is a `Std.HashMap`, whose `USize`
  indexing depends on the platform word size, which the kernel cannot
  evaluate; the RAT exhaustiveness check also uses a `Std.HashSet`. They are
  replaced here by checks over a list assignment (`KAssign`), with their own
  soundness proofs against the core CNF lemmas
  (`CNF.entails_clause_of_forall_sat`, `CNF.exists_sat_add_of_rat`, the
  entailment glue). Everything that runs in the kernel recurses structurally
  on lists; well-founded recursion (`Array.map`, index loops) is avoided.

  The checker is designed after `Std.Tactic.BVDecide.LRAT.check`: a clause id
  is its position (id `i` is slot `i - 1`), unknown or deleted hint ids fail,
  a RAT action whose pivot is not in its clause fails, and RAT hint groups must
  cover every live clause containing the negated pivot. Its soundness
  (`checkKernel_sound`) is proved on its own. Agreement with the core checker
  is tested, not proved, and it does not hold in general: the kernel checker
  accepts some certificates the core checker rejects. Example
  (`Tests/KernelTest.lean`): clauses `x`, `x ∨ ¬x`, `¬x` and one empty-clause
  step with hints 1, 2, 3. Here hint 2 propagates `x` (its literal `¬x` is
  false after hint 1), while core propagation returns an error on a hint
  clause that contains an atom in both polarities.

  Statements are about a Lean-defined `CNF Nat` term (the `lrat_reflect_cnf`
  form); `parseDimacs` itself does not kernel-reduce (byte-string slice
  iteration), so there is no kernel analogue of the parsed-file statement.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher

/-! ## List assignment and unit propagation -/

/-- Partial assignment of the kernel checker: the literals assumed true. -/
abbrev KAssign := List (Literal Nat)

/-- `a` agrees with every literal of `α`. -/
def KHolds (a : Nat → Bool) (α : KAssign) : Prop := ∀ l ∈ α, a l.1 = l.2

/-- Result of unit propagation: a conflict, an extended assignment, or a
    failed hint (not unit, unknown id). -/
inductive KProp where
  | conflict
  | extended (α : KAssign)
  | error

/-- What a propagation result guarantees for a total assignment `a` that
    satisfies the formula and the starting assignment. -/
def KProp.Sound (a : Nat → Bool) : KProp → Prop
  | .conflict => False
  | .extended α => KHolds a α
  | .error => True

/-- Propagate one hint clause: its literals not falsified by `α` must be
    none (conflict) or copies of one literal (which becomes true). -/
def unitOfK (α : KAssign) (lits : List (Literal Nat)) : KProp :=
  match lits.filter (fun l => !α.contains (l.1, !l.2)) with
  | [] => .conflict
  | l :: rest => if rest.all (· == l) then .extended (l :: α) else .error

/-- Propagate the hint clauses `hints` (clause ids) in order. -/
def propagateK (s : State) : KAssign → List Nat → KProp
  | α, [] => .extended α
  | α, h :: hs =>
    match s.get? h with
    | none => .error
    | some c =>
      match unitOfK α c.literals with
      | .conflict => .conflict
      | .extended α' => propagateK s α' hs
      | .error => .error

/-- The assignment falsifying every literal of `lits`. -/
def negLitsK (lits : List (Literal Nat)) : KAssign := lits.map fun l => (l.1, !l.2)

/-- `lits` contains a literal together with its negation. -/
def isTautK (lits : List (Literal Nat)) : Bool := lits.any fun l => lits.contains (l.1, !l.2)

/-- `r` is a conflict. -/
def isConflictK : KProp → Bool
  | .conflict => true
  | _ => false

/-! ## RUP and RAT checks -/

/-- RUP check: `c` is tautological, or its negation propagates to a conflict
    along `hints`. -/
def checkRupK (s : State) (c : CNF.Clause Nat) (hints : Array Nat) : Bool :=
  isTautK c.literals || isConflictK (propagateK s (negLitsK c.literals) hints.toList)

/-- Extend `α` by the negations of the literals of `ls` other than `np`;
    `none` if one of them is already true. -/
def extendWithoutK (α : KAssign) (np : Literal Nat) : List (Literal Nat) → Option KAssign
  | [] => some α
  | l :: ls =>
    if l == np then extendWithoutK α np ls
    else if α.contains l then none
    else extendWithoutK ((l.1, !l.2) :: α) np ls

/-- Every live clause containing `np` has its id (slot + 1) in `ids`;
    `i` is the slot of the head of the list. -/
def ratExhaustiveK (ids : List Nat) (np : Literal Nat) :
    List (Option (CNF.Clause Nat)) → Nat → Bool
  | [], _ => true
  | none :: rest, i => ratExhaustiveK ids np rest (i + 1)
  | some c :: rest, i =>
    (!c.literals.contains np || ids.contains (i + 1)) && ratExhaustiveK ids np rest (i + 1)

/-- RAT check on pivot `p`, as `State.checkRat`: `p ∈ c`; then `c` is
    tautological, or RUP along `rupHints`, or the RAT hint groups cover every
    live clause with `¬p` and each resolvent propagates to a conflict. -/
def checkRatK (s : State) (c : CNF.Clause Nat) (p : Literal Nat) (rupHints : Array Nat)
    (ratHints : Array (Nat × Array Nat)) : Bool :=
  if !c.literals.contains p then false
  else if isTautK c.literals then true
  else
    match propagateK s (negLitsK c.literals) rupHints.toList with
    | .conflict => true
    | .error => false
    | .extended α =>
      ratExhaustiveK (ratHints.toList.map (·.1)) p.negate s.formula.toList 0 &&
      ratHints.toList.all fun (idx, hints) =>
        match s.get? idx with
        | none => false
        | some c' =>
          match extendWithoutK α p.negate c'.literals with
          | none => true
          | some α' => isConflictK (propagateK s α' hints.toList)

/-! ## The checker -/

/-- DIMACS integer to 0-based literal (`0` has none). -/
def intLitK : Int → Option (Literal Nat)
  | .ofNat 0 => none
  | .ofNat (n + 1) => some (n, true)
  | .negSucc n => some (n, false)

/-- Clause conversion of the core checker, on the `Int` constructors. -/
def convertClauseK (clause : Array Int) : CNF.Clause Nat :=
  .ofLiterals (clause.toList.filterMap intLitK)

/-- Run a certificate; `true` iff the empty clause is derived. -/
def runK (s : State) : List IntAction → Bool
  | [] => false
  | .addEmpty _ hints :: _ => checkRupK s .empty hints
  | .addRup _ c hints :: rest =>
    checkRupK s (convertClauseK c) hints && runK (s.add (convertClauseK c)) rest
  | .addRat _ c p rup rat :: rest =>
    checkRatK s (convertClauseK c) (p.1 - 1, p.2) rup rat &&
      runK (s.add (convertClauseK c)) rest
  | .del ids :: rest => runK (s.deleteMany ids) rest

/-- `State.ofCNF` without `Array.map`. -/
def initK (cnf : CNF Nat) : State := ⟨⟨cnf.clauses.toList.map some⟩⟩

/-- Kernel-mode LRAT check: every reduction step is kernel-friendly, so
    `checkKernel cnf proof = true` can be discharged with `decide +kernel`.
    Designed after `Std.Tactic.BVDecide.LRAT.check` and sound on its own
    (`checkKernel_sound`); it accepts some certificates the core checker
    rejects (see the module docstring). -/
def checkKernel (cnf : CNF Nat) (proof : List IntAction) : Bool :=
  runK (initK cnf) proof

/-! ## Soundness -/

theorem unitOfK_sound {a : Nat → Bool} {α : KAssign} {lits : List (Literal Nat)}
    (hα : KHolds a α) (hl : ∃ l ∈ lits, a l.1 = l.2) : (unitOfK α lits).Sound a := by
  obtain ⟨m, hm, hma⟩ := hl
  have hmf : (!α.contains (m.1, !m.2)) = true := by
    cases hc : α.contains (m.1, !m.2)
    · rfl
    · have := hα _ (List.contains_iff_mem.mp hc)
      simp only at this
      rw [this] at hma
      cases hm2 : m.2 <;> simp_all
  have hmem : m ∈ lits.filter (fun l => !α.contains (l.1, !l.2)) :=
    List.mem_filter.mpr ⟨hm, hmf⟩
  unfold unitOfK
  split
  · next h => rw [h] at hmem; simp at hmem
  · next l rest h =>
    split
    · next hall =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [h] at hmem
        rcases List.mem_cons.mp hmem with rfl | hmr
        · exact hma
        · have := List.all_eq_true.mp hall m hmr
          simp only [beq_iff_eq] at this
          subst this
          exact hma
      · exact hα x hx
    · trivial

theorem propagateK_sound {s : State} {a : Nat → Bool} (hs : s.toCNF.Sat a) :
    ∀ {α : KAssign} {hints : List Nat}, KHolds a α → (propagateK s α hints).Sound a := by
  intro α hints hα
  induction hints generalizing α with
  | nil => exact hα
  | cons h hints ih =>
    unfold propagateK
    split
    · trivial
    · next c hc =>
      have hcs : c.Sat a := CNF.sat_of_mem hs (State.mem_toCNF_of_eq_some hc)
      have hu := unitOfK_sound (lits := c.literals) hα (CNF.Clause.sat_iff_exists_mem_eq.mp hcs)
      split
      · next heq => rw [heq] at hu; exact hu
      · next α' heq => rw [heq] at hu; exact ih hu
      · trivial

theorem false_of_isConflictK {r : KProp} {a : Nat → Bool} (h : isConflictK r = true)
    (hs : r.Sound a) : False := by
  cases r <;> simp_all [isConflictK, KProp.Sound]

theorem holds_negLitsK {a : Nat → Bool} {c : CNF.Clause Nat} (h : ¬ c.Sat a) :
    KHolds a (negLitsK c.literals) := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  have := CNF.Clause.not_sat_iff_forall_mem_ne.mp h m hm
  revert this
  cases a m.1 <;> cases m.2 <;> simp

theorem sat_of_isTautK {c : CNF.Clause Nat} (h : isTautK c.literals = true) :
    ∀ a, c.Sat a := by
  obtain ⟨l, hl, hl'⟩ := List.any_eq_true.mp h
  exact CNF.Clause.sat_of_mem_of_mem_neg (atom := l.1) (pol := l.2) hl
    (List.contains_iff_mem.mp hl')

/-- A conflict from the negation of `c` means `c` is entailed. -/
theorem entails_of_propagateK_conflict {s : State} {c : CNF.Clause Nat} {hints : List Nat}
    (h : propagateK s (negLitsK c.literals) hints = .conflict) :
    s.toCNF.EntailsClause c := by
  rw [CNF.entails_clause_def]
  intro a ha
  apply Classical.byContradiction
  intro hn
  have hp := propagateK_sound ha (hints := hints) (holds_negLitsK hn)
  rw [h] at hp
  exact hp

theorem entails_of_checkRupK {s : State} {c : CNF.Clause Nat} {hints : Array Nat}
    (h : checkRupK s c hints = true) : s.toCNF.EntailsClause c := by
  simp only [checkRupK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact CNF.entails_clause_of_forall_sat (sat_of_isTautK h)
  · rw [CNF.entails_clause_def]
    intro a ha
    apply Classical.byContradiction
    intro hn
    exact false_of_isConflictK h (propagateK_sound ha (holds_negLitsK hn))

theorem extendWithoutK_some {a : Nat → Bool} {np : Literal Nat} :
    ∀ {α α' : KAssign} {ls : List (Literal Nat)}, extendWithoutK α np ls = some α' →
      KHolds a α → (∀ l ∈ ls, l ≠ np → a l.1 = !l.2) → KHolds a α' := by
  intro α α' ls
  induction ls generalizing α with
  | nil =>
    intro h hα _
    simp only [extendWithoutK, Option.some.injEq] at h
    subst h
    exact hα
  | cons l ls ih =>
    intro h hα hls
    have hls' : ∀ x ∈ ls, x ≠ np → a x.1 = !x.2 := fun x hx => hls x (List.mem_cons_of_mem _ hx)
    simp only [extendWithoutK] at h
    split at h
    · exact ih h hα hls'
    · next hne =>
      split at h
      · simp at h
      · apply ih h ?_ hls'
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hls l List.mem_cons_self (fun heq => hne (by simp [heq]))
        · exact hα x hx

theorem extendWithoutK_none {a : Nat → Bool} {np : Literal Nat} :
    ∀ {α : KAssign} {ls : List (Literal Nat)}, extendWithoutK α np ls = none →
      KHolds a α → ∃ l ∈ ls, l ≠ np ∧ a l.1 = l.2 := by
  intro α ls
  induction ls generalizing α with
  | nil => intro h; simp [extendWithoutK] at h
  | cons l ls ih =>
    intro h hα
    simp only [extendWithoutK] at h
    split at h
    · obtain ⟨x, hx, hne, hxa⟩ := ih h hα
      exact ⟨x, List.mem_cons_of_mem _ hx, hne, hxa⟩
    · next hne =>
      have hne' : l ≠ np := fun heq => hne (by simp [heq])
      split at h
      · next hc =>
        exact ⟨l, List.mem_cons_self, hne', hα l (List.contains_iff_mem.mp hc)⟩
      · by_cases hla : a l.1 = l.2
        · exact ⟨l, List.mem_cons_self, hne', hla⟩
        · have hα' : KHolds a ((l.1, !l.2) :: α) := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · revert hla
              cases a l.1 <;> cases l.2 <;> simp
            · exact hα x hx
          obtain ⟨x, hx, hxne, hxa⟩ := ih h hα'
          exact ⟨x, List.mem_cons_of_mem _ hx, hxne, hxa⟩

theorem ratExhaustiveK_spec {ids : List Nat} {np : Literal Nat} :
    ∀ {l : List (Option (CNF.Clause Nat))} {i : Nat}, ratExhaustiveK ids np l i = true →
      ∀ (j : Nat) (hj : j < l.length) (c : CNF.Clause Nat), l[j] = some c →
        np ∈ c.literals → i + j + 1 ∈ ids := by
  intro l
  induction l with
  | nil => intro i _ j hj; simp at hj
  | cons o rest ih =>
    intro i h j hj c hc hnp
    cases o with
    | none =>
      simp only [ratExhaustiveK] at h
      cases j with
      | zero => simp at hc
      | succ j =>
        have := ih h j (by simpa using hj) c (by simpa using hc) hnp
        rwa [show i + (j + 1) + 1 = i + 1 + j + 1 by omega]
    | some c0 =>
      simp only [ratExhaustiveK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Option.some.injEq] at hc
        subst hc
        rcases h.1 with h1 | h1
        · have := List.contains_iff_mem.mpr hnp
          simp_all
        · simpa using List.contains_iff_mem.mp h1
      | succ j =>
        have := ih h.2 j (by simpa using hj) c (by simpa using hc) hnp
        rwa [show i + (j + 1) + 1 = i + 1 + j + 1 by omega]

theorem checkRatK_spec {s : State} {c : CNF.Clause Nat} {p : Literal Nat}
    {rupHints : Array Nat} {ratHints : Array (Nat × Array Nat)}
    (h : checkRatK s c p rupHints ratHints = true) :
    p ∈ c ∧ ∀ c' ∈ s.toCNF, p.negate ∈ c' →
      s.toCNF.EntailsClause (c ++ c'.erase p.negate) := by
  unfold checkRatK at h
  split at h
  · simp at h
  · next hp =>
    have hpc : p ∈ c := by
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hp
      exact List.contains_iff_mem.mp hp
    refine ⟨hpc, ?_⟩
    intro c' hc' hnp
    split at h
    · next ht =>
      exact CNF.entails_clause_append_left (CNF.entails_clause_of_forall_sat (sat_of_isTautK ht))
    · split at h
      · next hcf => exact CNF.entails_clause_append_left (entails_of_propagateK_conflict hcf)
      · simp at h
      · next α hext =>
        simp only [Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨hex, hall⟩ := h
        obtain ⟨i, hi, hci⟩ := State.exists_getElem_eq_some_of_mem hc'
        have hmem := ratExhaustiveK_spec hex i (by simpa using hi) c' (by simpa using hci) hnp
        obtain ⟨⟨idx, hints⟩, hrat, hidx⟩ := List.mem_map.mp hmem
        simp only [Nat.zero_add] at hidx
        have hget : s.get? idx = some c' := by
          rw [hidx]
          exact State.get?_add_one_of_getElem_eq_some hi hci
        have h1 := hall (idx, hints) hrat
        simp only [hget] at h1
        rw [CNF.entails_clause_def]
        intro a ha
        apply Classical.byContradiction
        intro hn
        rw [CNF.Clause.sat_append] at hn
        have hnc : ¬ c.Sat a := fun h => hn (Or.inl h)
        have hnd : ¬ (c'.erase p.negate).Sat a := fun h => hn (Or.inr h)
        have hα : KHolds a α := by
          have := propagateK_sound ha (hints := rupHints.toList) (holds_negLitsK hnc)
          rw [hext] at this
          exact this
        split at h1
        · next hnone =>
          obtain ⟨l, hl, hne, hla⟩ := extendWithoutK_none hnone hα
          exact hnd (CNF.Clause.sat_of_mem_of_eq
            (CNF.Clause.mem_erase_iff.mpr ⟨Ne.symm hne, hl⟩) hla)
        · next α' hsome =>
          have hα' := extendWithoutK_some hsome hα (by
            intro l hl hne
            have := CNF.Clause.not_sat_iff_forall_mem_ne.mp hnd l
              (CNF.Clause.mem_erase_iff.mpr ⟨Ne.symm hne, hl⟩)
            revert this
            cases a l.1 <;> cases l.2 <;> simp)
          exact false_of_isConflictK h1 (propagateK_sound ha hα')

theorem runK_sound : ∀ {s : State} {proof : List IntAction},
    runK s proof = true → s.toCNF.Unsat := by
  intro s proof h
  induction proof generalizing s with
  | nil => simp [runK] at h
  | cons act rest ih =>
    cases act with
    | addEmpty _ hints =>
      simp only [runK] at h
      exact CNF.unsat_of_entails_clause_unsat CNF.Clause.unsat_empty (entails_of_checkRupK h)
    | addRup _ c hints =>
      simp only [runK, Bool.and_eq_true] at h
      exact CNF.unsat_of_entails_unsat (ih h.2)
        (State.entails_add_of_entails_clause (entails_of_checkRupK h.1))
    | addRat _ c p rup rat =>
      simp only [runK, Bool.and_eq_true] at h
      have hspec := checkRatK_spec h.1
      have hu := ih h.2
      rw [State.add_toCNF_eq_toCNF_add] at hu
      exact CNF.unsat_of_forall_exists (CNF.exists_sat_add_of_rat hspec.1 hspec.2) hu
    | del ids =>
      simp only [runK] at h
      exact CNF.unsat_of_entails_unsat (ih h) State.entails_deleteMany

theorem initK_toCNF (cnf : CNF Nat) : (initK cnf).toCNF = cnf := by
  rw [CNF.Internal.ext_iff]
  show Array.filterMap id (⟨cnf.clauses.toList.map some⟩ : Array _) = cnf.clauses
  apply Array.toList_inj.mp
  simp [List.filterMap_map]

theorem checkKernel_sound (cnf : CNF Nat) (proof : List IntAction)
    (h : checkKernel cnf proof = true) : cnf.Unsat := by
  have := runK_sound h
  rwa [initK_toCNF] at this

end LRATCatcher
