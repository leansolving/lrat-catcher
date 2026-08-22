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

/-- Result of checking one chunk: the updated clause database, or `refuted`
    if the chunk derived the empty clause. -/
inductive ChunkOut (n : Nat) where
  | more (f : DefaultFormula n)
  | refuted

/-- Process a certificate chunk from `idx` on, threading the clause database.
    Mirrors `compactLratChecker.go` (including its skips: unconvertible
    actions and RAT actions whose pivot is missing), but returns the final
    state instead of discarding it; `none` on a failed check. -/
def runChunk {n : Nat} (f : DefaultFormula n) (chunk : Array IntAction) (idx : Nat) :
    Option (ChunkOut n) :=
  if h : idx < chunk.size then
    match intActionToDefaultClauseAction n chunk[idx] with
    | none => runChunk f chunk (idx + 1)
    | some (.addEmpty _ rupHints) =>
      let (_, ok) := Formula.performRupAdd f Clause.empty rupHints
      if ok then some .refuted else none
    | some (.addRup _ c rupHints) =>
      let (f', ok) := Formula.performRupAdd f c rupHints
      if ok then runChunk f' chunk (idx + 1) else none
    | some (.addRat _ c pivot rupHints ratHints) =>
      if pivot ∈ Clause.toList c then
        let (f', ok) := Formula.performRatAdd f c pivot rupHints ratHints
        if ok then runChunk f' chunk (idx + 1) else none
      else
        runChunk f chunk (idx + 1)
    | some (.del ids) => runChunk (Formula.delete f ids) chunk (idx + 1)
  else
    some (.more f)

/-- A refuting chunk makes the incoming state unsatisfiable
    (mirrors `compactLratChecker`'s `go_sound`). -/
theorem runChunk_refuted_sound {n : Nat} (f : DefaultFormula n) (chunk : Array IntAction)
    (idx : Nat) (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    runChunk f chunk idx = some .refuted → Unsatisfiable (PosFin n) f := by
  fun_induction runChunk
  case case1 => rename_i ih; apply ih <;> assumption
  case case2 =>
    rename_i hints _ _ heq
    intro _
    apply addEmptyCaseSound (rupHints := hints)
    · assumption
    · simp [heq]
  case case3 => simp
  case case4 => grind [Unsatisfiable, Liff]
  case case5 => simp
  case case6 => grind [Equisat, Clause.limplies_iff_mem]
  case case7 => simp
  case case8 => rename_i ih; apply ih <;> assumption
  case case9 =>
    rename_i ih
    intro h3 p pf
    apply ih (by grind) (by grind) h3 p
    apply Formula.limplies_delete
    assumption
  case case10 => simp

/-- A non-refuting chunk hands over a state that is ready for the next chunk
    and whose unsatisfiability transfers back to the incoming state. -/
theorem runChunk_more_sound {n : Nat} (f : DefaultFormula n) (chunk : Array IntAction)
    (idx : Nat) {f' : DefaultFormula n}
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    runChunk f chunk idx = some (.more f') →
      Formula.ReadyForRupAdd f' ∧ Formula.ReadyForRatAdd f' ∧
        (Unsatisfiable (PosFin n) f' → Unsatisfiable (PosFin n) f) := by
  fun_induction runChunk
  case case1 => rename_i ih; apply ih <;> assumption
  case case2 => simp
  case case3 => simp
  case case4 => grind [Unsatisfiable, Liff]
  case case5 => simp
  case case6 => grind [Equisat, Clause.limplies_iff_mem]
  case case7 => simp
  case case8 => rename_i ih; apply ih <;> assumption
  case case9 =>
    rename_i ih
    intro h3
    obtain ⟨r1, r2, himp⟩ := ih (by grind) (by grind) h3
    exact ⟨r1, r2, fun hu =>
      limplies_unsat _ _ Formula.limplies_delete (himp hu)⟩
  case case10 =>
    intro h
    simp only [Option.some.injEq, ChunkOut.more.injEq] at h
    subst h
    exact ⟨h1, h2, id⟩

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

/-- Plain-data image of a checker state between chunks: clause literal lists,
    with `none` holes preserved (clause IDs are positions). -/
abbrev Snapshot := List (Option (List (Nat × Bool)))

/-- Render a snapshot as text: one line per clause position — `.` for a hole,
    otherwise the clause as signed integers terminated by `0` (variable =
    `PosFin` value = original DIMACS variable, sign = polarity). Snapshots are
    untrusted data plumbing (a wrong snapshot fails the Boolean step checks),
    so the codec needs no round-trip proof. -/
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

/-- Strip a clause database down to plain data (positions preserved). -/
def serialize {n : Nat} (f : DefaultFormula n) : Snapshot :=
  (f.clauses.map (Option.map fun c => c.clause.map fun l => (l.1.val, l.2))).toList

/-- Rebuild literals over `PosFin n`; fails on out-of-range variables. -/
def restoreLits (n : Nat) : List (Nat × Bool) → Option (List (Literal (PosFin n)))
  | [] => some []
  | (v, b) :: rest =>
    if h : 0 < v ∧ v < n then
      (restoreLits n rest).map (fun ls => (⟨v, h⟩, b) :: ls)
    else
      none

private theorem nodupkey_of_no_compl {n : Nat} {ls : List (Literal (PosFin n))}
    (h : ∀ l ∈ ls, (l.1, !l.2) ∉ ls) :
    ∀ l : PosFin n, (l, true) ∉ ls ∨ (l, false) ∉ ls := by
  intro l
  by_cases h1 : (l, true) ∈ ls
  · exact Or.inr (by simpa using h (l, true) h1)
  · exact Or.inl h1

/-- Rebuild one clause; fails on out-of-range, duplicate, or complementary
    literals (`serialize` output always passes). -/
def restoreClause (n : Nat) (ls0 : List (Nat × Bool)) : Option (DefaultClause n) := do
  let ls ← restoreLits n ls0
  if h : ls.Nodup ∧ ∀ l ∈ ls, (l.1, !l.2) ∉ ls then
    some ⟨ls, nodupkey_of_no_compl h.2, h.1⟩
  else
    none

/-- Rebuild the clause array from a snapshot, position by position. -/
def restoreList (n : Nat) : Snapshot → Option (List (Option (DefaultClause n)))
  | [] => some []
  | none :: rest => (restoreList n rest).map (none :: ·)
  | some ls :: rest => do
    let c ← restoreClause n ls
    let cs ← restoreList n rest
    return some c :: cs

/-- Tail-recursive `restoreList`, substituted at compilation (`@[csimp]`).
    Snapshots keep one position per clause *id* (holes included), so at
    GB-certificate scale they have millions of positions and the naive
    recursion overflows the native stack (SIGABRT inside `native_decide`). -/
private def restoreListTR (n : Nat) : Snapshot → Option (List (Option (DefaultClause n))) :=
  go #[]
where
  go (acc : Array (Option (DefaultClause n))) :
      Snapshot → Option (List (Option (DefaultClause n)))
  | [] => some acc.toList
  | none :: rest => go (acc.push none) rest
  | some ls :: rest =>
    match restoreClause n ls with
    | some c => go (acc.push (some c)) rest
    | none => none

private theorem restoreListTR.go_eq {n : Nat} (snap : Snapshot)
    (acc : Array (Option (DefaultClause n))) :
    restoreListTR.go n acc snap = (restoreList n snap).map (acc.toList ++ ·) := by
  induction snap generalizing acc with
  | nil => simp [restoreListTR.go, restoreList]
  | cons hd tl ih =>
    cases hd with
    | none =>
      rw [restoreListTR.go, ih, restoreList]
      cases restoreList n tl <;> simp
    | some ls =>
      rw [restoreListTR.go]
      cases hc : restoreClause n ls with
      | none => simp [restoreList, hc]
      | some c =>
        simp only [ih, restoreList, hc]
        cases restoreList n tl <;> simp

@[csimp] private theorem restoreList_eq_restoreListTR :
    @restoreList = @restoreListTR := by
  funext n snap
  rw [restoreListTR, restoreListTR.go_eq]
  cases restoreList n snap <;> simp

/-- Restore a checker state from a snapshot. Invalid snapshots restore to the
    empty (satisfiable) formula, which is sound: soundness lemmas only ever
    *assume* unsatisfiability of a restored state. Readiness holds for both
    branches via `readyForRupAdd_ofArray`/`readyForRatAdd_ofArray`. -/
def restoreD (n : Nat) (snap : Snapshot) : DefaultFormula n :=
  match restoreList n snap with
  | some cs => Formula.ofArray cs.toArray
  | none => Formula.ofArray #[]

/-- A restored state is always ready for further chunks (both `restoreD`
    branches go through `Formula.ofArray`). -/
theorem restoreD_ready {n : Nat} (snap : Snapshot) :
    Formula.ReadyForRupAdd (restoreD n snap) ∧ Formula.ReadyForRatAdd (restoreD n snap) := by
  unfold restoreD
  split <;> exact ⟨Formula.readyForRupAdd_ofArray _, Formula.readyForRatAdd_ofArray _⟩

private theorem units_empty_of_ready {n : Nat} {f : DefaultFormula n}
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    f.rupUnits = #[] ∧ f.ratUnits = #[] := by
  have h1' : DefaultFormula.ReadyForRupAdd f := h1
  have h2' : DefaultFormula.ReadyForRatAdd f := h2
  unfold DefaultFormula.ReadyForRupAdd at h1'
  unfold DefaultFormula.ReadyForRatAdd at h2'
  exact ⟨h1'.1, h2'.1⟩

/-! ## Roundtrip: `restoreD` after `serialize` preserves the model set -/

private theorem restoreLits_serialize {n : Nat} (ls : List (Literal (PosFin n))) :
    restoreLits n (ls.map fun l => (l.1.val, l.2)) = some ls := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
    obtain ⟨⟨v, hv⟩, b⟩ := l
    simp [restoreLits, ih, hv]

private theorem restoreClause_serialize {n : Nat} (c : DefaultClause n) :
    restoreClause n (c.clause.map fun l => (l.1.val, l.2)) = some c := by
  obtain ⟨cl, hkey, hnodup⟩ := c
  simp [restoreClause, restoreLits_serialize, hnodup]
  grind

private theorem restoreList_serialize {n : Nat} (cs : List (Option (DefaultClause n))) :
    restoreList n (cs.map (Option.map fun c => c.clause.map fun l => (l.1.val, l.2)))
      = some cs := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | none => simp [restoreList, ih]
    | some c => simp [restoreList, ih, restoreClause_serialize]

private theorem restoreList_serialize_eq {n : Nat} (f : DefaultFormula n) :
    restoreList n (serialize f) = some f.clauses.toList := by
  simp only [serialize, Array.toList_map]
  exact restoreList_serialize f.clauses.toList

private theorem restoreD_serialize {n : Nat} (f : DefaultFormula n) :
    restoreD n (serialize f) = (Formula.ofArray f.clauses : DefaultFormula n) := by
  simp [restoreD, restoreList_serialize_eq]

private theorem liff_ofArray_units {n : Nat} (f : DefaultFormula n)
    (hrup : f.rupUnits = #[]) (hrat : f.ratUnits = #[]) :
    Liff (PosFin n) (Formula.ofArray f.clauses : DefaultFormula n) f := by
  intro p
  rw [Formula.sat_iff_forall, Formula.sat_iff_forall]
  have ht : Formula.toList (Formula.ofArray f.clauses : DefaultFormula n)
      = Formula.toList f := by
    show DefaultFormula.toList (DefaultFormula.ofArray f.clauses) = DefaultFormula.toList f
    simp [DefaultFormula.toList, DefaultFormula.ofArray, hrup, hrat]
  rw [ht]

/-! ## Compaction: hole-free snapshots preserve the model set

`serialize` keeps one position per clause id, holes included, so the snapshot
of a long run carries every id the solver ever allocated even though almost
all of those clauses are deleted. `compactSnapshot` drops the holes (order
preserved). The lemmas below show that a compacted snapshot restores to a
formula with the same clause list as the verbatim one, so unsatisfiability
transfers across a compacting boundary exactly as across a verbatim boundary.
Positions shift, so the ids and hints of all subsequent chunks must be
renumbered to match; that renumbering is data preparation, not trusted code —
a wrong id or hint makes the per-chunk check fail, never succeed. -/

/-- Drop the holes of a snapshot, preserving the order of live clauses. -/
def compactSnapshot (snap : Snapshot) : Snapshot :=
  (snap.filterMap id).map some

private theorem restoreList_compact {n : Nat} (snap : Snapshot) :
    restoreList n (compactSnapshot snap)
      = (restoreList n snap).map (fun cs => (cs.filterMap id).map some) := by
  induction snap with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | none =>
      have hc : compactSnapshot (none :: tl) = compactSnapshot tl := by
        simp [compactSnapshot]
      rw [hc, ih, restoreList]
      cases restoreList n tl <;> simp
    | some ls =>
      have hc : compactSnapshot (some ls :: tl) = some ls :: compactSnapshot tl := by
        simp [compactSnapshot]
      rw [hc, restoreList, restoreList, ih]
      cases restoreClause n ls <;> cases restoreList n tl <;> simp

private theorem toList_ofArray {n : Nat} (cs : Array (Option (DefaultClause n))) :
    DefaultFormula.toList (Formula.ofArray cs : DefaultFormula n)
      = cs.toList.filterMap id := by
  show DefaultFormula.toList (DefaultFormula.ofArray cs) = cs.toList.filterMap id
  simp [DefaultFormula.toList, DefaultFormula.ofArray]

/-- Restoring a compacted snapshot yields the same model set as the state the
    snapshot was taken from: the compacting analogue of the verbatim
    roundtrip. -/
theorem liff_restoreD_compactSnapshot_serialize {n : Nat} (f : DefaultFormula n)
    (hrup : f.rupUnits = #[]) (hrat : f.ratUnits = #[]) :
    Liff (PosFin n) (restoreD n (compactSnapshot (serialize f))) f := by
  have hres : restoreList n (compactSnapshot (serialize f))
      = some ((f.clauses.toList.filterMap id).map some) := by
    rw [restoreList_compact, restoreList_serialize_eq, Option.map_some]
  intro p
  rw [Formula.sat_iff_forall, Formula.sat_iff_forall]
  have ht : Formula.toList (restoreD n (compactSnapshot (serialize f)))
      = Formula.toList f := by
    show DefaultFormula.toList (restoreD n (compactSnapshot (serialize f)))
      = DefaultFormula.toList f
    rw [restoreD, hres, toList_ofArray]
    simp [DefaultFormula.toList, hrup, hrat, List.filterMap_map]
  rw [ht]

/-! ## Per-module step checks -/

/-- First chunk: start from `cnf` (as the core checker does) and check that
    the chunk ends in the state imaged by `next`. -/
def stepStart (cnf : CNF Nat) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (CNF.convertLRAT cnf) chunk 0 with
  | some (.more f') => serialize f' == next
  | _ => false

/-- Middle chunk: resume from `prev`, check the chunk ends in `next`. -/
def stepMid (n : Nat) (prev : Snapshot) (chunk : Array IntAction) (next : Snapshot) : Bool :=
  match runChunk (restoreD n prev) chunk 0 with
  | some (.more f') => serialize f' == next
  | _ => false

/-- Last chunk: resume from `prev`, the chunk must derive the empty clause. -/
def stepFinish (n : Nat) (prev : Snapshot) (chunk : Array IntAction) : Bool :=
  match runChunk (restoreD n prev) chunk 0 with
  | some .refuted => true
  | _ => false

/-! ## Step soundness (composes to `cnf.Unsat`, one `native_decide` per chunk) -/

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

/-! ## Externalization (presolve/derivation handoff)

A chunk chain that ends in `more` (no empty clause) is a checked *derivation*
`F ⊢ F′` — the certified-presolve primitive. `externSnap` turns the final
snapshot into a `CNF Nat`, so the derived formula can be cubed and refuted
with the existing cube-and-conquer machinery (`checkCover`); the bridge
`extern_unsat_restoreD` transfers that refutation back to the snapshot state,
and the step soundness lemmas carry it back to the original formula. -/

/-- Externalize a snapshot as a `CNF Nat`: holes dropped, variables shifted
    back to the 0-indexed convention of `parseDimacs` (so `CNF.dimacs` renders
    it with the original DIMACS variable names). -/
def externSnap (snap : Snapshot) : CNF Nat :=
  { clauses := (snap.filterMap (Option.map (List.map fun (v, b) => (v - 1, b)))).toArray }

/-- A snapshot produced by a successful first step restores. -/
theorem stepStart_restores {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStart cnf chunk next = true) :
    (restoreList (cnf.numLiterals + 1) next).isSome := by
  unfold stepStart at h
  split at h
  next f' _ =>
    rw [(eq_of_beq h).symm, restoreList_serialize_eq]
    rfl
  next => simp at h

/-- A snapshot produced by a successful middle step restores. -/
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

/-- **Externalization bridge**: refuting the externalized snapshot refutes the
    restored checker state. The restorability side condition is supplied by
    `stepStart_restores`/`stepMid_restores` for step-produced snapshots. -/
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

/-- Derivation handoff, single-chunk derivation. -/
theorem stepStart_extern {cnf : CNF Nat} {chunk : Array IntAction} {next : Snapshot}
    (h : stepStart cnf chunk next = true) (hx : (externSnap next).Unsat) : cnf.Unsat :=
  stepStart_sound h (extern_unsat_restoreD (stepStart_restores h) hx)

/-- Derivation handoff after one or more chunks: compose with
    `stepMid_sound`/`stepStart_sound` down to the original formula. -/
theorem stepMid_extern {n : Nat} {prev : Snapshot} {chunk : Array IntAction} {next : Snapshot}
    (h : stepMid n prev chunk next = true) (hx : (externSnap next).Unsat) :
    Unsatisfiable (PosFin n) (restoreD n prev) :=
  stepMid_sound h (extern_unsat_restoreD (stepMid_restores h) hx)

/-! ## Padding tautology (chained-derivation composition)

When several derivations are chained (batch `i+1`'s base is batch `i`'s derived
formula plus a padding tautology clause, as a *term* rather than a file), the
padding clause `[v ∨ ¬v]` is a tautology satisfied by every assignment, so
appending it never changes satisfiability. `unsat_of_append_pad` peels it back
off, so downstream composition sees the *unpadded* base. -/

/-- The one-clause padding CNF `[[v, ¬v]]` — a tautology, satisfied by every
    assignment (same `(var, polarity)` convention as `CNF`). -/
def padCNF (v : Nat) : CNF Nat := { clauses := #[[(v, true), (v, false)]] }

/-- The padding clause is a tautology: it evaluates to `true` under every
    assignment. -/
theorem padCNF_eval (a : Nat → Bool) (v : Nat) : CNF.eval a (padCNF v) = true := by
  simp only [padCNF, CNF.eval, List.all_toArray, List.all_cons, List.all_nil,
    CNF.Clause.eval, List.any_cons, List.any_nil, Bool.and_true]
  cases a v <;> rfl

/-- Appending the padding tautology never changes satisfiability, so a
    refutation of `F ++ padCNF v` is a refutation of `F`. Used to peel the
    padding clause off a chained batch's base term. -/
theorem unsat_of_append_pad {F : CNF Nat} {v : Nat} :
    (F ++ padCNF v).Unsat → F.Unsat := by
  intro h a
  have hp := h a
  rw [CNF.eval_append, padCNF_eval, Bool.and_true] at hp
  exact hp

end LRATCatcher
