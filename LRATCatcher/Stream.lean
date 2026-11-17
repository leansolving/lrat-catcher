import LRATCatcher.Basic
import Std.Tactic.BVDecide.LRAT

/-!
  # LRATCatcher.Stream — resumable (chunked) LRAT checking

  The core checker (`Std.Tactic.BVDecide.LRAT.Internal.compactLratChecker`)
  consumes a whole certificate and returns only a verdict. This module adds a
  *resumable* variant: `runChunk` processes a certificate *prefix* and returns
  the intermediate clause database, so a large certificate can be checked as a
  chain of chunks — each discharged by its own `native_decide`, in its own
  module — with the composition a pure proof term.

  Between chunks the state crosses module boundaries as a `Snapshot`: the
  clause array with proof fields and the assignment cache stripped. Clause IDs
  are array positions, so snapshots preserve `none` holes verbatim; `restoreD`
  rebuilds the checker state via `Formula.ofArray` (readiness is
  `readyForRupAdd_ofArray`/`readyForRatAdd_ofArray`, for arbitrary arrays).

  Soundness is inherited from the public per-step lemmas of the core checker
  (`rupAdd_sound`/`Liff`, `ratAdd_sound`/`Equisat`, `limplies_delete`); no
  core code is duplicated. The per-module Boolean checks are `stepStart`
  (first chunk, from a `CNF Nat`), `stepMid`, and `stepFinish` (last chunk,
  must derive the empty clause); their soundness lemmas compose to
  `cnf.Unsat` with one `native_decide` axiom per chunk and nothing else.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher

/-! ## Resumable chunk checker -/

/-- Clause conversion of the core checker (`check.convertClause`, a helper
    local to `check` there): DIMACS integers to 0-based literals, zeros
    dropped. -/
def convertClause (clause : Array Int) : CNF.Clause Nat :=
  .ofLiterals <| clause.toList.filterMap fun int =>
    if int > 0 then
      some (int.natAbs - 1, true)
    else if int < 0 then
      some (int.natAbs - 1, false)
    else
      none

/-- Result of checking one action or one chunk: the updated clause database,
    or `refuted` if the empty clause was derived. -/
inductive ChunkOut where
  | more (s : State)
  | refuted

/-- One action, as one iteration of the core checker's loop (`check.go`);
    `none` on a failed check. -/
def step (s : State) : IntAction → Option ChunkOut
  | .addEmpty _ rupHints => if s.checkEmpty rupHints then some .refuted else none
  | .addRup _ clause rupHints =>
    let c := convertClause clause
    if s.checkRup c rupHints then some (.more (s.add c)) else none
  | .addRat _ clause pivot rupHints ratHints =>
    let c := convertClause clause
    if s.checkRat c ⟨pivot.1 - 1, pivot.2⟩ rupHints ratHints then some (.more (s.add c))
    else none
  | .del ids => some (.more (s.deleteMany ids))

theorem step_refuted_sound {s : State} {a : IntAction} :
    step s a = some .refuted → s.toCNF.Unsat := by
  intro h
  cases a with
  | addEmpty _ rupHints =>
    simp only [step] at h
    split at h
    · rename_i hc
      exact CNF.unsat_of_entails_clause_unsat (c := .empty) (by simp)
        (State.entails_clause_empty_of_checkEmpty hc)
    · simp at h
  | addRup =>
    simp only [step] at h
    split at h <;> simp at h
  | addRat =>
    simp only [step] at h
    split at h <;> simp at h
  | del => simp [step] at h

theorem step_more_sound {s s' : State} {a : IntAction} :
    step s a = some (.more s') → s'.toCNF.Unsat → s.toCNF.Unsat := by
  intro h hu
  cases a with
  | addEmpty =>
    simp only [step] at h
    split at h <;> simp at h
  | addRup _ clause rupHints =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, ChunkOut.more.injEq] at h
      subst h
      exact CNF.unsat_of_entails_unsat hu
        (State.entails_add_of_entails_clause (State.entails_clause_of_checkRup hc))
    · simp at h
  | addRat _ clause pivot rupHints ratHints =>
    simp only [step] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, ChunkOut.more.injEq] at h
      subst h
      exact CNF.unsat_of_forall_exists
        (fun _ ha => State.unsat_of_unsat_of_checkRat hc ha) hu
    · simp at h
  | del ids =>
    simp only [step, Option.some.injEq, ChunkOut.more.injEq] at h
    subst h
    exact CNF.unsat_of_entails_unsat hu State.entails_deleteMany

/-- Process a certificate chunk from `idx` on, threading the clause database.
    Mirrors the core checker's loop, but returns the final state instead of
    discarding it: `some (.more s')` when the chunk is exhausted,
    `some .refuted` when it derives the empty clause, `none` on a failed
    check. -/
def runChunk (s : State) (chunk : Array IntAction) (idx : Nat) : Option ChunkOut :=
  if h : idx < chunk.size then
    match step s chunk[idx] with
    | some .refuted => some .refuted
    | some (.more s') => runChunk s' chunk (idx + 1)
    | none => none
  else
    some (.more s)
termination_by chunk.size - idx

/-- A refuting chunk makes the incoming state unsatisfiable. -/
theorem runChunk_refuted_sound {s : State} {chunk : Array IntAction} {idx : Nat} :
    runChunk s chunk idx = some .refuted → s.toCNF.Unsat := by
  fun_induction runChunk s chunk idx with
  | case1 s idx hidx hstep => intro _; exact step_refuted_sound hstep
  | case2 s idx hidx s' hstep ih => intro h; exact step_more_sound hstep (ih h)
  | case3 => simp
  | case4 => simp

/-- A non-refuting chunk hands over a state whose unsatisfiability transfers
    back to the incoming state. -/
theorem runChunk_more_sound {s s' : State} {chunk : Array IntAction} {idx : Nat} :
    runChunk s chunk idx = some (.more s') → s'.toCNF.Unsat → s.toCNF.Unsat := by
  fun_induction runChunk s chunk idx with
  | case1 => simp
  | case2 s idx hidx s'' hstep ih => intro h hu; exact step_more_sound hstep (ih h hu)
  | case3 => simp
  | case4 s idx hidx =>
    intro h hu
    simp only [Option.some.injEq, ChunkOut.more.injEq] at h
    subst h
    exact hu

/-! ## LRAT text helper -/

/-- drat-trim's forward-mode LRAT (needed for *derivations*, e.g. symmetry-breaking clause batches) writes additions that introduce a
    fresh definition variable as RAT steps with ZERO resolution candidates
    and hence an EMPTY hint list. The core parser routes every hint-less
    addition to `addRup`, whose check fails on empty hints. Reroute such
    actions to `addRat` with the standard first-literal pivot (the same
    choice the core parser's `getPivot` makes for genuine RAT lines):
    `performRatAdd` with zero RAT groups still validates the addition (it
    checks there is no resolution candidate on the pivot), so this stays
    checker-validated — a bogus empty-hint addition still fails. Identity
    on every other action. -/
def normalizeAction (a : IntAction) : IntAction :=
  match a with
  | .addRup id c hints =>
    if hints.isEmpty && !c.isEmpty then
      let p := c[0]!
      .addRat id c (p.natAbs, decide (p > 0)) #[] #[]
    else
      .addRup id c hints
  | a => a

/-- Parse LRAT text into actions; `#[]` on failure. A failed parse can only
    make the Boolean step checks fail, so this is sound. Empty-hint
    additions are normalized to pivot-RAT steps (see `normalizeAction`). -/
def parseActions (s : String) : Array IntAction :=
  match parseLRATProof s.toUTF8 with
  | .ok p => p.map normalizeAction
  | .error _ => #[]

/-! ## Snapshots -/

/-- Plain-data image of a checker state between chunks: position `i` holds
    the clause with id `i` as a literal list, `none` where there is no live
    clause (deleted ids, and id `0`, which no clause has). Variables are
    1-based, as in DIMACS. -/
abbrev Snapshot := List (Option (List (Nat × Bool)))

/-- Render a snapshot as text: one line per clause position — `.` for a hole,
    otherwise the clause as signed integers terminated by `0` (variable =
    original DIMACS variable, sign = polarity). Snapshots are untrusted data
    plumbing (a wrong snapshot fails the Boolean step checks), so the codec
    needs no round-trip proof. -/
def printSnap (snap : Snapshot) : String :=
  String.join <| snap.map fun
    | none => ".\n"
    | some ls =>
      String.join (ls.map fun (v, b) => if b then s!"{v} " else s!"-{v} ") ++ "0\n"

/-- Parse a `printSnap` rendering: `.` lines are holes, other lines are read
    as signed integers up to the terminating `0`; blank lines and non-integer
    tokens are ignored. -/
def parseSnap (s : String) : Snapshot := Id.run do
  let mut snap : Snapshot := []
  for line in s.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty then
      continue
    if t == "." then
      snap := none :: snap
    else
      let mut ls : List (Nat × Bool) := []
      for tok in t.split (fun ch => ch == ' ' || ch == '\t') do
        match tok.toInt? with
        | some 0 => break
        | some l => ls := (l.natAbs, decide (0 < l)) :: ls
        | none => pure ()
      snap := some ls.reverse :: snap
  return snap.reverse

/-- Strip a checker state down to plain data. The core checker stores the
    clause with id `i` in slot `i - 1`; the leading hole shifts this so that
    snapshot position `i` is id `i`, and variables are written 1-based. -/
def serialize (s : State) : Snapshot :=
  none :: (s.formula.map (Option.map fun c => c.literals.map fun l => (l.1 + 1, l.2))).toList

/-- Rebuild one clause from its snapshot literals (variables shifted back to
    0-based). -/
def restoreClause (ls : List (Nat × Bool)) : CNF.Clause Nat :=
  .ofLiterals (ls.map fun l => (l.1 - 1, l.2))

/-- Restore a checker state from a snapshot: drop position `0`, rebuild each
    clause. Total: every snapshot restores to some state, which is sound
    because the soundness lemmas only ever *assume* unsatisfiability of a
    restored state. -/
def restoreD (snap : Snapshot) : State :=
  ⟨snap.tail.toArray.map (Option.map restoreClause)⟩

theorem restoreClause_serialize (c : CNF.Clause Nat) :
    restoreClause (c.literals.map fun l => (l.1 + 1, l.2)) = c := by
  simp [restoreClause, List.map_map, Function.comp_def]

/-- **Roundtrip**: restoring a serialized state gives the state back. -/
theorem restoreD_serialize (s : State) : restoreD (serialize s) = s := by
  obtain ⟨formula⟩ := s
  simp [restoreD, serialize, Function.comp_def, Option.map_map, restoreClause_serialize]

/-! ## Compaction: hole-free snapshots preserve the clause list

`serialize` keeps one position per clause id, holes included, so the snapshot
of a long run carries every id the solver ever allocated even though almost
all of those clauses are deleted. `compactSnapshot` drops the holes (order
preserved). A compacted snapshot restores to a state with the same clause
list as the state it was taken from, so unsatisfiability transfers across a
compacting boundary exactly as across a verbatim boundary. Positions shift,
so the ids and hints of all subsequent chunks must be renumbered to match;
that renumbering is data preparation, not trusted code — a wrong id or hint
makes the per-chunk check fail, never succeed. -/

/-- Drop the holes of a snapshot, preserving the order of live clauses. The
    leading `none` stands for id `0`, so the `r`-th live clause lands at
    position `r` (id `r`) and the next clause the checker adds gets id
    `live + 1`. -/
def compactSnapshot (snap : Snapshot) : Snapshot :=
  none :: (snap.filterMap id).map some

/-- Restoring a compacted snapshot yields a state with the same CNF as the
    state the snapshot was taken from: the compacting analogue of
    `restoreD_serialize`. -/
theorem toCNF_restoreD_compactSnapshot_serialize (s : State) :
    (restoreD (compactSnapshot (serialize s))).toCNF = s.toCNF := by
  obtain ⟨formula⟩ := s
  simp only [restoreD, compactSnapshot, serialize, State.toCNF, List.tail_cons]
  congr 1
  apply Array.toList_inj.mp
  simp [List.filterMap_map, List.map_filterMap, Function.comp_def, restoreClause_serialize,
    List.filterMap_filterMap]
  congr 1
  funext o
  cases o <;> rfl

/- PORT (v4.36.0): A4 in progress
/ -! ## Per-module step checks - /

/ -- First chunk: start from `cnf` (as the core checker does) and check that
    the chunk ends in the state imaged by `next`. - /
def stepStart (cnf : CNF Nat) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (CNF.convertLRAT cnf) chunk 0 with
  | some (.more f') => serialize f' == next
  | _ => false

/ -- Middle chunk: resume from `prev`, check the chunk ends in `next`. - /
def stepMid (n : Nat) (prev : Snapshot) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (restoreD n prev) chunk 0 with
  | some (.more f') => serialize f' == next
  | _ => false

/ -- Last chunk: resume from `prev`, the chunk must derive the empty clause. - /
def stepFinish (n : Nat) (prev : Snapshot) (chunk : Array IntAction) : Bool :=
  match runChunk (restoreD n prev) chunk 0 with
  | some .refuted => true
  | _ => false

/ -- Compacting variant of `stepStart`: the boundary snapshot is hole-free
    (`compactSnapshot`), so the id space restarts at the live-clause count.
    The ids and hints of all subsequent chunks must be renumbered to the
    compacted positions — untrusted data preparation: a wrong renumbering
    fails a step check, never succeeds. - /
def stepStartC (cnf : CNF Nat) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (CNF.convertLRAT cnf) chunk 0 with
  | some (.more f') => compactSnapshot (serialize f') == next
  | _ => false

/ -- Compacting variant of `stepMid` (see `stepStartC`). `prev` may itself be
    a compacted snapshot — `restoreD` does not care. - /
def stepMidC (n : Nat) (prev : Snapshot) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (restoreD n prev) chunk 0 with
  | some (.more f') => compactSnapshot (serialize f') == next
  | _ => false

/ -! ## Step soundness (composes to `cnf.Unsat`, one `native_decide` per chunk) - /

theorem stepStart_sound {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStart cnf chunk next = true) :
    Unsatisfiable (PosFin (cnf.numLiterals + 1)) (restoreD (cnf.numLiterals + 1) next) →
      cnf.Unsat := by
  unfold stepStart at h
  split at h
  next f' heq =>
    have hnext : next = serialize f' := (eq_of_beq h).symm
    obtain ⟨r1, r2, himp⟩ := runChunk_more_sound _ _ _
      (CNF.convertLRAT_readyForRupAdd cnf) (CNF.convertLRAT_readyForRatAdd cnf) heq
    obtain ⟨hu1, hu2⟩ := units_empty_of_ready r1 r2
    intro hunsat
    apply CNF.unsat_of_convertLRAT_unsat
    apply himp
    rw [hnext, restoreD_serialize] at hunsat
    exact (liff_unsat _ _ (liff_ofArray_units f' hu1 hu2)).mp hunsat
  next => simp at h

theorem stepMid_sound {n : Nat} {prev : Snapshot} {chunk : Array IntAction} {next : Snapshot}
    (h : stepMid n prev chunk next = true) :
    Unsatisfiable (PosFin n) (restoreD n next) →
      Unsatisfiable (PosFin n) (restoreD n prev) := by
  unfold stepMid at h
  split at h
  next f' heq =>
    have hnext : next = serialize f' := (eq_of_beq h).symm
    obtain ⟨hready, hmore⟩ := restoreD_ready (n := n) prev
    obtain ⟨r1, r2, himp⟩ := runChunk_more_sound _ _ _ hready hmore heq
    obtain ⟨hu1, hu2⟩ := units_empty_of_ready r1 r2
    intro hunsat
    apply himp
    rw [hnext, restoreD_serialize] at hunsat
    exact (liff_unsat _ _ (liff_ofArray_units f' hu1 hu2)).mp hunsat
  next => simp at h

theorem stepFinish_sound {n : Nat} {prev : Snapshot} {chunk : Array IntAction}
    (h : stepFinish n prev chunk = true) :
    Unsatisfiable (PosFin n) (restoreD n prev) := by
  unfold stepFinish at h
  split at h
  next heq =>
    obtain ⟨hready, hmore⟩ := restoreD_ready (n := n) prev
    exact runChunk_refuted_sound _ _ _ hready hmore heq
  next => simp at h

theorem stepStartC_sound {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStartC cnf chunk next = true) :
    Unsatisfiable (PosFin (cnf.numLiterals + 1)) (restoreD (cnf.numLiterals + 1) next) →
      cnf.Unsat := by
  unfold stepStartC at h
  split at h
  next f' heq =>
    have hnext : next = compactSnapshot (serialize f') := (eq_of_beq h).symm
    obtain ⟨r1, r2, himp⟩ := runChunk_more_sound _ _ _
      (CNF.convertLRAT_readyForRupAdd cnf) (CNF.convertLRAT_readyForRatAdd cnf) heq
    obtain ⟨hu1, hu2⟩ := units_empty_of_ready r1 r2
    intro hunsat
    apply CNF.unsat_of_convertLRAT_unsat
    apply himp
    rw [hnext] at hunsat
    exact (liff_unsat _ _ (liff_restoreD_compactSnapshot_serialize f' hu1 hu2)).mp hunsat
  next => simp at h

theorem stepMidC_sound {n : Nat} {prev : Snapshot} {chunk : Array IntAction} {next : Snapshot}
    (h : stepMidC n prev chunk next = true) :
    Unsatisfiable (PosFin n) (restoreD n next) →
      Unsatisfiable (PosFin n) (restoreD n prev) := by
  unfold stepMidC at h
  split at h
  next f' heq =>
    have hnext : next = compactSnapshot (serialize f') := (eq_of_beq h).symm
    obtain ⟨hready, hmore⟩ := restoreD_ready (n := n) prev
    obtain ⟨r1, r2, himp⟩ := runChunk_more_sound _ _ _ hready hmore heq
    obtain ⟨hu1, hu2⟩ := units_empty_of_ready r1 r2
    intro hunsat
    apply himp
    rw [hnext] at hunsat
    exact (liff_unsat _ _ (liff_restoreD_compactSnapshot_serialize f' hu1 hu2)).mp hunsat
  next => simp at h

/ -! ## Externalization (presolve/derivation handoff)

A chunk chain that ends in `more` (no empty clause) is a checked *derivation*
`F ⊢ F′` — the certified-presolve primitive. `externSnap` turns the final
snapshot into a `CNF Nat`, so the derived formula can be cubed and refuted
with the existing cube-and-conquer machinery (`checkCover`); the bridge
`extern_unsat_restoreD` transfers that refutation back to the snapshot state,
and the step soundness lemmas carry it back to the original formula. - /

/ -- Externalize a snapshot as a `CNF Nat`: holes dropped, variables shifted
    back to the 0-indexed convention of `parseDimacs` (so `CNF.dimacs` renders
    it with the original DIMACS variable names). - /
def externSnap (snap : Snapshot) : CNF Nat :=
  { clauses := (snap.filterMap (Option.map (List.map fun (v, b) => (v - 1, b)))).toArray }

/ -- A snapshot produced by a successful first step restores. - /
theorem stepStart_restores {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStart cnf chunk next = true) :
    (restoreList (cnf.numLiterals + 1) next).isSome := by
  unfold stepStart at h
  split at h
  next f' _ =>
    rw [(eq_of_beq h).symm, restoreList_serialize_eq]
    rfl
  next => simp at h

/ -- A snapshot produced by a successful middle step restores. - /
theorem stepMid_restores {n : Nat} {prev : Snapshot} {chunk : Array IntAction} {next : Snapshot}
    (h : stepMid n prev chunk next = true) :
    (restoreList n next).isSome := by
  unfold stepMid at h
  split at h
  next f' _ =>
    rw [(eq_of_beq h).symm, restoreList_serialize_eq]
    rfl
  next => simp at h

private theorem restoreLits_val {n : Nat} :
    ∀ {ls : List (Nat × Bool)} {lits : List (Literal (PosFin n))},
      restoreLits n ls = some lits → ls = lits.map fun l => (l.1.val, l.2) := by
  intro ls
  induction ls with
  | nil =>
    intro lits h
    simp only [restoreLits, Option.some.injEq] at h
    simp [← h]
  | cons hd tl ih =>
    intro lits h
    obtain ⟨v, b⟩ := hd
    simp only [restoreLits] at h
    split at h
    · cases htl : restoreLits n tl with
      | none => rw [htl] at h; simp at h
      | some tll =>
        rw [htl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp [← ih htl]
    · simp at h

private theorem sat_restoreClause {n : Nat} {p : PosFin n → Bool} {ls : List (Nat × Bool)}
    {c : DefaultClause n} (hc : restoreClause n ls = some c) (hp : p ⊨ c) :
    CNF.Clause.eval (fun u => if h : 0 < u + 1 ∧ u + 1 < n then p ⟨u + 1, h⟩ else false)
      (ls.map fun (v, b) => (v - 1, b)) = true := by
  simp only [restoreClause, Option.bind_eq_bind, Option.bind_eq_some_iff] at hc
  obtain ⟨lits, hlits, hdite⟩ := hc
  split at hdite
  · simp only [Option.some.injEq] at hdite
    obtain ⟨l, hmem, hsat⟩ := (Clause.sat_iff_exists p c).mp hp
    rw [← hdite] at hmem
    simp only [Clause.toList, DefaultClause.toList] at hmem
    obtain ⟨⟨v, hv⟩, b⟩ := l
    have hsat' : p ⟨v, hv⟩ = b := hsat
    have hls : (v - 1, b) ∈ ls.map fun (v, b) => (v - 1, b) := by
      rw [restoreLits_val hlits]
      exact List.mem_map.mpr ⟨((⟨v, hv⟩ : PosFin n), b),
        List.mem_map.mpr ⟨(⟨⟨v, hv⟩, b⟩ : Literal (PosFin n)), hmem, rfl⟩, rfl⟩
    simp only [CNF.Clause.eval, List.any_eq_true]
    refine ⟨(v - 1, b), hls, ?_⟩
    have hv1 : v - 1 + 1 = v := Nat.sub_add_cancel hv.1
    grind
  · simp at hdite

private theorem eval_externSnap_cons_none (a : Nat → Bool) (tl : Snapshot) :
    CNF.eval a (externSnap (none :: tl)) = CNF.eval a (externSnap tl) := by
  simp [externSnap, CNF.eval]

private theorem eval_externSnap_cons_some (a : Nat → Bool) (ls : List (Nat × Bool))
    (tl : Snapshot) :
    CNF.eval a (externSnap (some ls :: tl))
      = (CNF.Clause.eval a (ls.map fun (v, b) => (v - 1, b))
          && CNF.eval a (externSnap tl)) := by
  simp [externSnap, CNF.eval]

private theorem extern_eval_of_restore {n : Nat} {p : PosFin n → Bool} :
    ∀ {snap : Snapshot} {cs : List (Option (DefaultClause n))},
      restoreList n snap = some cs →
      (∀ c : DefaultClause n, some c ∈ cs → p ⊨ c) →
      CNF.eval (fun u => if h : 0 < u + 1 ∧ u + 1 < n then p ⟨u + 1, h⟩ else false)
        (externSnap snap) = true := by
  intro snap
  induction snap with
  | nil =>
    intro cs _ _
    simp [externSnap, CNF.eval]
  | cons hd tl ih =>
    intro cs h hsat
    cases hd with
    | none =>
      simp only [restoreList] at h
      cases htl : restoreList n tl with
      | none => rw [htl] at h; simp at h
      | some cs' =>
        rw [htl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [eval_externSnap_cons_none]
        exact ih htl (fun c hc => hsat c (List.mem_cons_of_mem _ hc))
    | some ls =>
      simp only [restoreList, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨c, hc, h⟩ := h
      obtain ⟨cs', hcs', h⟩ := h
      subst h
      have hhd := sat_restoreClause hc (hsat c (List.mem_cons_self ..))
      have htl := ih hcs' (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc'))
      rw [eval_externSnap_cons_some, hhd, htl]
      rfl

/ -- **Externalization bridge**: refuting the externalized snapshot refutes the
    restored checker state. The restorability side condition is supplied by
    `stepStart_restores`/`stepMid_restores` for step-produced snapshots. - /
theorem extern_unsat_restoreD {n : Nat} {snap : Snapshot}
    (hres : (restoreList n snap).isSome)
    (hx : (externSnap snap).Unsat) :
    Unsatisfiable (PosFin n) (restoreD n snap) := by
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp hres
  intro p hp
  rw [restoreD] at hp
  simp only [hcs] at hp
  have hall : ∀ c : DefaultClause n, some c ∈ cs → p ⊨ c := by
    rw [Formula.sat_iff_forall] at hp
    intro c hc
    apply hp
    show c ∈ DefaultFormula.toList (DefaultFormula.ofArray cs.toArray)
    simp only [DefaultFormula.toList, DefaultFormula.ofArray,
      List.toList_toArray, List.map_nil, List.append_nil, List.mem_filterMap]
    exact ⟨some c, hc, rfl⟩
  have heval := extern_eval_of_restore hcs hall
  have hfalse := hx (fun u => if h : 0 < u + 1 ∧ u + 1 < n then p ⟨u + 1, h⟩ else false)
  rw [heval] at hfalse
  exact Bool.noConfusion hfalse

/ -- Derivation handoff, single-chunk derivation. - /
theorem stepStart_extern {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStart cnf chunk next = true) (hx : (externSnap next).Unsat) : cnf.Unsat :=
  stepStart_sound h (extern_unsat_restoreD (stepStart_restores h) hx)

/ -- Derivation handoff after one or more chunks: compose with
    `stepMid_sound`/`stepStart_sound` down to the original formula. - /
theorem stepMid_extern {n : Nat} {prev : Snapshot} {chunk : Array IntAction} {next : Snapshot}
    (h : stepMid n prev chunk next = true) (hx : (externSnap next).Unsat) :
    Unsatisfiable (PosFin n) (restoreD n prev) :=
  stepMid_sound h (extern_unsat_restoreD (stepMid_restores h) hx)

/ -! ## Padding tautology (chained-derivation composition)

When several derivations are chained (batch `i+1`'s base is batch `i`'s derived
formula plus a padding tautology clause, as a *term* rather than a file), the
padding clause `[v ∨ ¬v]` is a tautology satisfied by every assignment, so
appending it never changes satisfiability. `unsat_of_append_pad` peels it back
off, so downstream composition sees the *unpadded* base. - /

/ -- The one-clause padding CNF `[[v, ¬v]]` — a tautology, satisfied by every
    assignment (same `(var, polarity)` convention as `CNF`). - /
def padCNF (v : Nat) : CNF Nat := { clauses := #[[(v, true), (v, false)]] }

/ -- The padding clause is a tautology: it evaluates to `true` under every
    assignment. - /
theorem padCNF_eval (a : Nat → Bool) (v : Nat) : CNF.eval a (padCNF v) = true := by
  simp only [padCNF, CNF.eval, List.all_toArray, List.all_cons, List.all_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.and_true]
  cases a v <;> rfl

/ -- Appending the padding tautology never changes satisfiability, so a
    refutation of `F ++ padCNF v` is a refutation of `F`. Used to peel the
    padding clause off a chained batch's base term. - /
theorem unsat_of_append_pad {F : CNF Nat} {v : Nat} :
    (F ++ padCNF v).Unsat → F.Unsat := by
  intro h a
  have hp := h a
  rw [CNF.eval_append, padCNF_eval, Bool.and_true] at hp
  exact hp

-/

end LRATCatcher
