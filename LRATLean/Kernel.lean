import LRATLean.Basic
import Std.Tactic.BVDecide.LRAT

/-!
  # LRATLean.Kernel — kernel-mode LRAT checking (zero compiler trust)

  A variant of the LRAT check whose Boolean evaluation reduces inside the
  Lean *kernel* (`decide +kernel`), so the compiled evaluator (`native_decide`)
  is not part of the trust base. Soundness is inherited from the verified
  checker in Lean core (`lratCheckerSound`).

  The core checker as shipped does not kernel-reduce; four constructs block
  whnf in the kernel and are replaced here by kernel-reducible equivalents:

  * `compactLratChecker` recurses by counting an index *up*, i.e. well-founded
    recursion (`Acc.rec` is opaque to kernel reduction) → use the structurally
    recursive `lratChecker` from Lean core instead;
  * `DefaultClause.ofArray` builds clauses through `Std.HashMap` (USize
    hashing is platform-opaque) → `mkClauseK` below, with decidable
    duplicate/tautology checks;
  * `CNF.relabelFin` branches on a classically-decided existential →
    `liftK` below targets `numLiterals + 2`, which always has a fallback
    element, so no nonemptiness case split is needed;
  * `Array.map` / `Array.mapM` / `Array.filter` / `Array.range` are
    well-founded recursions (only `Array.foldl`, `push`, `modify`, `set!`,
    `getElem` reduce) → all wrappers below stay on `List`; the one use inside
    the core checker's RAT path (`ratHintsExhaustive`) is cloned as
    `ratHintsExhaustiveK` and proved equal, so RAT steps work in kernel mode.

  Statements are about a Lean-defined `CNF Nat` term (the `lrat_reflect_cnf`
  form); `parseDimacs` itself does not kernel-reduce (byte-string slice
  iteration), so there is no kernel analogue of the parsed-file statement.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATLean

/-! ## Kernel-reducible clause construction -/

private theorem nodupkey_of_no_compl {n : Nat} {ls : List (Literal (PosFin n))}
    (h : ∀ l ∈ ls, (l.1, !l.2) ∉ ls) :
    ∀ l : PosFin n, (l, true) ∉ ls ∨ (l, false) ∉ ls := by
  intro l
  by_cases h1 : (l, true) ∈ ls
  · exact Or.inr (h (l, true) h1)
  · exact Or.inl h1

/-- Kernel-reducible replacement for `DefaultClause.ofArray`: deduplicate,
    then reject tautologies. The decidable side conditions provide the
    `DefaultClause` invariants directly. -/
def mkClauseK {n : Nat} (ls : List (Literal (PosFin n))) : Option (DefaultClause n) :=
  if h : ls.eraseDups.Nodup ∧ ∀ l ∈ ls.eraseDups, (l.1, !l.2) ∉ ls.eraseDups then
    some ⟨ls.eraseDups, nodupkey_of_no_compl h.2, h.1⟩
  else
    none

theorem mkClauseK_clause {n : Nat} {ls : List (Literal (PosFin n))} {c : DefaultClause n}
    (h : mkClauseK ls = some c) : c.clause = ls.eraseDups := by
  simp only [mkClauseK] at h
  split at h
  · cases h; rfl
  · simp at h

/-- Kernel-reducible replacement for `intActionToDefaultClauseAction`
    (which uses `Array.mapM` and the HashMap-based `Clause.ofArray`). -/
def intActionToDCAK (n : Nat) : IntAction → Option (DefaultClauseAction n)
  | .addEmpty cId rupHints => some <| .addEmpty cId rupHints
  | .addRup cId c rupHints => do
    let c ← c.toList.mapM intToLiteral
    let c ← mkClauseK c
    return .addRup cId c rupHints
  | .addRat cId c pivot rupHints ratHints => do
    let pivot ← natLiteralToPosFinLiteral pivot
    let c ← c.toList.mapM intToLiteral
    let c ← mkClauseK c
    return .addRat cId c pivot rupHints ratHints
  | .del ids => return .del ids

/-! ## Kernel-reducible CNF conversion -/

/-- The relabeling function underlying `liftK`. -/
def liftFun (cnf : CNF Nat) (v : Nat) : PosFin (cnf.numLiterals + 2) :=
  if h : v < cnf.numLiterals then ⟨v + 1, by omega⟩
  else ⟨cnf.numLiterals + 1, by omega⟩

/-- Kernel-reducible replacement for `CNF.lift`: shifts variables by 1 into
    `PosFin (numLiterals + 2)`. Targeting `numLiterals + 2` (instead of `+ 1`)
    guarantees the fallback element `numLiterals + 1` exists, avoiding
    `relabelFin`'s classically-decided nonemptiness existential. -/
def liftK (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 2)) :=
  ⟨(cnf.clauses.toList.map (CNF.Clause.relabel (liftFun cnf))).toArray⟩

theorem liftK_eq (cnf : CNF Nat) : liftK cnf = CNF.relabel (liftFun cnf) cnf := by
  simp only [liftK, CNF.relabel]
  rw [← Array.toList_map, Array.toArray_toList]

theorem unsat_of_liftK_unsat (cnf : CNF Nat) : (liftK cnf).Unsat → cnf.Unsat := by
  rw [liftK_eq]
  intro h
  apply (CNF.unsat_relabel_iff ?_).mp h
  intro v1 v2 hv1 hv2 heq
  have h1 := CNF.lt_numLiterals hv1
  have h2 := CNF.lt_numLiterals hv2
  simp only [liftFun, h1, h2, reduceDIte] at heq
  have heq' : v1 + 1 = v2 + 1 := congrArg Subtype.val heq
  omega

/-- Kernel-reducible replacement for `CNF.convertLRAT'`. -/
def convertClausesK {n : Nat} (cls : List (CNF.Clause (PosFin n))) :
    List (Option (DefaultClause n)) :=
  cls.filterMap (fun cl => (mkClauseK cl).map some)

/-- Kernel-reducible replacement for `CNF.convertLRAT`. As there, the leading
    `none` aligns formula indices with 1-based LRAT clause ids. -/
def convertK (cnf : CNF Nat) : DefaultFormula (cnf.numLiterals + 2) :=
  DefaultFormula.ofArray (none :: convertClausesK (liftK cnf).clauses.toList).toArray

theorem readyForRupAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRupAdd (convertK cnf) :=
  DefaultFormula.readyForRupAdd_ofArray _

theorem readyForRatAdd_convertK (cnf : CNF Nat) :
    DefaultFormula.ReadyForRatAdd (convertK cnf) :=
  DefaultFormula.readyForRatAdd_ofArray _

theorem unsat_of_convertK_unsat (cnf : CNF Nat) :
    Unsatisfiable (PosFin (cnf.numLiterals + 2)) (convertK cnf) → cnf.Unsat := by
  intro h1
  apply unsat_of_liftK_unsat
  intro assignment
  replace h1 := (unsat_of_cons_none_unsat _ h1) assignment
  apply eq_false_of_ne_true
  intro h2
  apply h1
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro lratClause hlclause
  simp only [Formula.toList, DefaultFormula.toList, DefaultFormula.ofArray,
    List.toList_toArray, List.map_nil, List.append_nil, convertClausesK,
    List.filterMap_filterMap, List.mem_filterMap] at hlclause
  rcases hlclause with ⟨reflectClause, hrclause1, hrclause2⟩
  have hmk : mkClauseK reflectClause = some lratClause := by
    cases hcase : mkClauseK reflectClause <;> simp_all
  simp only [CNF.eval, Array.all_eq_true'] at h2
  have heval := h2 reflectClause (by simpa using hrclause1)
  simp only [CNF.Clause.eval, List.any_eq_true] at heval
  rcases heval with ⟨lit, hlit1, hlit2⟩
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq]
  refine ⟨lit, ?_, by simp_all⟩
  simp only [Clause.toList, DefaultClause.toList, mkClauseK_clause hmk]
  exact List.mem_eraseDups.mpr hlit1

/-! ## Kernel-reducible RAT path

The only kernel-opaque construct inside the core checker's run path is
`DefaultFormula.ratHintsExhaustive` (`Array.range`/`filter`/`map`). The three
definitions below clone `ratHintsExhaustive`, `performRatAdd`, and
`lratChecker` with a `List`-based exhaustiveness check and are proved equal
to the originals, so `lratCheckerSound` transfers. -/

/-- Kernel-reducible clone of `DefaultFormula.getRatClauseIndices`. -/
def getRatClauseIndicesK {n : Nat} (clauses : Array (Option (DefaultClause n)))
    (l : Literal (PosFin n)) : List Nat :=
  (List.range clauses.size).filter (fun i =>
    match clauses[i]! with
    | none => false
    | some c => c.contains (Literal.negate l))

theorem getRatClauseIndicesK_eq {n : Nat} (clauses : Array (Option (DefaultClause n)))
    (l : Literal (PosFin n)) :
    getRatClauseIndicesK clauses l
      = (DefaultFormula.getRatClauseIndices clauses l).toList := by
  simp only [getRatClauseIndicesK, DefaultFormula.getRatClauseIndices,
    Array.toList_filter, Array.toList_range]
  rfl

/-- Kernel-reducible clone of `DefaultFormula.ratHintsExhaustive`. -/
def ratHintsExhaustiveK {n : Nat} (f : DefaultFormula n) (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) : Bool :=
  getRatClauseIndicesK f.clauses pivot = ratHints.toList.map (fun x => x.1)

theorem ratHintsExhaustiveK_eq {n : Nat} (f : DefaultFormula n) (pivot : Literal (PosFin n))
    (ratHints : Array (Nat × Array Nat)) :
    ratHintsExhaustiveK f pivot ratHints
      = DefaultFormula.ratHintsExhaustive f pivot ratHints := by
  unfold ratHintsExhaustiveK DefaultFormula.ratHintsExhaustive
  apply decide_eq_decide.mpr
  rw [getRatClauseIndicesK_eq, ← Array.toList_map, Array.toList_inj]

/-- Clone of `DefaultFormula.performRatAdd` calling `ratHintsExhaustiveK`;
    the body is otherwise verbatim. -/
def performRatAddK {n : Nat} (f : DefaultFormula n) (c : DefaultClause n)
    (pivot : Literal (PosFin n)) (rupHints : Array Nat)
    (ratHints : Array (Nat × Array Nat)) :
    DefaultFormula n × Bool :=
  if ratHintsExhaustiveK f pivot ratHints then
    let negC := DefaultClause.negate c
    let (f, contradictionFound) := DefaultFormula.insertRupUnits f negC
    if contradictionFound then (f, false)
    else
      let (f, derivedLits, derivedEmpty, encounteredError) :=
        DefaultFormula.performRupCheck f rupHints
      if encounteredError then (f, false)
      else if derivedEmpty then (f, false)
      else
        let fold_fn := fun (acc : DefaultFormula n × Bool) ratHint =>
          if acc.2 then DefaultFormula.performRatCheck acc.1 (Literal.negate pivot) ratHint
          else (acc.1, false)
        let (f, allChecksPassed) := ratHints.foldl fold_fn (f, true)
        if !allChecksPassed then (f, false)
        else
          match f with
          | ⟨clauses, rupUnits, ratUnits, assignments⟩ =>
            let assignments := DefaultFormula.restoreAssignments assignments derivedLits
            let f := DefaultFormula.clearRupUnits ⟨clauses, rupUnits, ratUnits, assignments⟩
            (f.insert c, true)
  else (f, false)

theorem performRatAddK_eq {n : Nat} (f : DefaultFormula n) (c : DefaultClause n)
    (pivot : Literal (PosFin n)) (rupHints : Array Nat)
    (ratHints : Array (Nat × Array Nat)) :
    performRatAddK f c pivot rupHints ratHints
      = DefaultFormula.performRatAdd f c pivot rupHints ratHints := by
  unfold performRatAddK DefaultFormula.performRatAdd
  rw [ratHintsExhaustiveK_eq]

/-- Kernel-reducible clone of the structurally recursive `lratChecker`,
    instantiated at `DefaultFormula` and calling `performRatAddK`. -/
def lratCheckerK {n : Nat} (f : DefaultFormula n) (prf : List (DefaultClauseAction n)) :
    Result :=
  match prf with
  | [] => .outOfProof
  | .addEmpty _ rupHints :: _ =>
    let (_, checkSuccess) := DefaultFormula.performRupAdd f DefaultClause.empty rupHints
    if checkSuccess then .success else .rupFailure
  | .addRup _ c rupHints :: restPrf =>
    let (f, checkSuccess) := DefaultFormula.performRupAdd f c rupHints
    if checkSuccess then lratCheckerK f restPrf else .rupFailure
  | .addRat _ c pivot rupHints ratHints :: restPrf =>
    let (f, checkSuccess) := performRatAddK f c pivot rupHints ratHints
    if checkSuccess then lratCheckerK f restPrf else .rupFailure
  | .del ids :: restPrf => lratCheckerK (DefaultFormula.delete f ids) restPrf

theorem lratCheckerK_eq {n : Nat} (f : DefaultFormula n)
    (prf : List (DefaultClauseAction n)) :
    lratCheckerK f prf = lratChecker f prf := by
  induction prf generalizing f with
  | nil => rfl
  | cons a restPrf ih =>
    cases a with
    | addEmpty id rupHints => rfl
    | addRup id c rupHints =>
      simp only [lratCheckerK, lratChecker, ih]
    | addRat id c pivot rupHints ratHints =>
      simp only [lratCheckerK, lratChecker, performRatAddK_eq, ih]
    | del ids =>
      simp only [lratCheckerK, lratChecker, ih]
      rfl

/-! ## The kernel-mode check and its soundness -/

/-- Kernel-mode LRAT check: every reduction step is kernel-friendly, so
    `checkKernel cnf proof = true` can be discharged with `decide +kernel`.
    Mirrors `Std.Tactic.BVDecide.LRAT.check` up to the replacements above;
    RAT actions whose pivot is not in the clause are dropped (they are
    skipped by the reference checker as well). -/
def checkKernel (cnf : CNF Nat) (proof : List IntAction) : Bool :=
  let actions := proof.filterMap (intActionToDCAK (cnf.numLiterals + 2))
  let actions := actions.filter (fun a =>
    match a with
    | .addRat _ c pivot _ _ => c.contains pivot
    | _ => true)
  lratCheckerK (convertK cnf) actions = .success

theorem checkKernel_sound (cnf : CNF Nat) (proof : List IntAction)
    (h : checkKernel cnf proof = true) : cnf.Unsat := by
  apply unsat_of_convertK_unsat
  simp only [checkKernel, lratCheckerK_eq, decide_eq_true_eq] at h
  apply lratCheckerSound _ (readyForRupAdd_convertK cnf) (readyForRatAdd_convertK cnf) _ ?_ h
  intro a ha
  have hfil := (List.mem_filter.mp ha).2
  cases a with
  | addEmpty id rupHints => trivial
  | addRup id c rupHints => trivial
  | del ids => trivial
  | addRat id c pivot rupHints ratHints =>
    simp only [WellFormedAction]
    rw [Clause.limplies_iff_mem]
    exact (DefaultClause.contains_iff c pivot).mp (by simpa using hfil)

end LRATLean
