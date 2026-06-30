import LRATCatcher.Reflect

/-!
  # Verified Ramsey encoding

  End-to-end verified Ramsey bounds: Lean encodes "K_n has a 2-coloring with
  no red K_s and no blue K_t" as a CNF, an external SAT solver refutes it, and
  the LRAT certificate yields `¬ hasRamseyFreeColoring n s t` — a statement
  about edge colorings, not about CNF. `¬ hasRamseyFreeColoring n s t` is the
  upper bound `R(s,t) ≤ n`; the lower bound `R(s,t) > n` is an explicit
  witness coloring checked by `native_decide`.

  Encoding (edge variables `edgeVar n i j` for `0 ≤ i < j < n`, row-major
  upper-triangle indexing; variable true = edge red, false = blue):
  * for each s-subset of vertices, "some edge blue" (negative clause);
  * for each t-subset of vertices, "some edge red" (positive clause).
  Unlike the Schur encoding there is no translation layer between colorings
  and assignments: an edge 2-coloring *is* an assignment to the edge
  variables, so the encoding soundness proof uses the coloring directly as
  the CNF valuation.

  The DIMACS file for the solver is produced by `lratcatch-gen ramsey n s t
  out` from the *same* `encode` function, so the certified CNF and the solved
  CNF coincide by construction.
-/

open Lean Elab Command
open Std.Sat

namespace LRATCatcher.Ramsey

/-! ## Edge variables, subsets, and encoding -/

/-- Number of edge variables for `K_n`: `C(n,2)`. -/
def numEdgeVars (n : Nat) : Nat := n * (n - 1) / 2

/-- Variable index of edge `(i,j)` with `0 ≤ i < j < n` (0-based, row-major
    upper triangle). Injective on that domain (checked in the test file). -/
def edgeVar (n i j : Nat) : Nat := i * (2 * n - i - 1) / 2 + (j - i - 1)

/-- All s-element subsets of `{0,…,n-1}`, as strictly decreasing lists. -/
def subsets : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, s + 1 => (subsets n s).map (n :: ·) ++ subsets n (s + 1)

/-- Edge variables of the clique on vertex list `vs`. -/
def cliqueEdgeVars (n : Nat) (vs : List Nat) : List Nat :=
  vs.flatMap fun i =>
    vs.filterMap fun j =>
      if i < j then some (edgeVar n i j) else none

/-- Clause "some edge of this clique is blue (false)". -/
def redClause (n : Nat) (vs : List Nat) : CNF.Clause Nat :=
  (cliqueEdgeVars n vs).map fun v => (v, false)

/-- Clause "some edge of this clique is red (true)". -/
def blueClause (n : Nat) (vs : List Nat) : CNF.Clause Nat :=
  (cliqueEdgeVars n vs).map fun v => (v, true)

/-- CNF encoding of "`K_n` has a 2-coloring with no red `K_s` and no blue
    `K_t`". -/
def encode (n s t : Nat) : CNF Nat :=
  let red := (subsets n s).map (redClause n)
  let blue := (subsets n t).map (blueClause n)
  { clauses := (red ++ blue).toArray }

/-! ## Mathematical predicates -/

/-- No red `K_s`: no `s` distinct vertices below `n` with all edges true. -/
def noRedClique (n s : Nat) (f : Nat → Bool) : Prop :=
  ∀ vs : List Nat, vs.length = s → (∀ v ∈ vs, v < n) → vs.Nodup →
    ¬(∀ i j, i ∈ vs → j ∈ vs → i < j → f (edgeVar n i j) = true)

/-- No blue `K_t`: no `t` distinct vertices below `n` with all edges false. -/
def noBlueClique (n t : Nat) (f : Nat → Bool) : Prop :=
  ∀ vs : List Nat, vs.length = t → (∀ v ∈ vs, v < n) → vs.Nodup →
    ¬(∀ i j, i ∈ vs → j ∈ vs → i < j → f (edgeVar n i j) = false)

/-- `f` is a Ramsey-free coloring: no red `K_s`, no blue `K_t`. -/
def isRamseyFree (n s t : Nat) (f : Nat → Bool) : Prop :=
  noRedClique n s f ∧ noBlueClique n t f

/-- `K_n` admits a 2-coloring with no red `K_s` and no blue `K_t`;
    `¬ hasRamseyFreeColoring n s t` states the upper bound `R(s,t) ≤ n`. -/
def hasRamseyFreeColoring (n s t : Nat) : Prop :=
  ∃ f : Nat → Bool, isRamseyFree n s t f

/-! ## Encoding soundness -/

/-- Lists enumerated by `subsets n s` have length `s`, entries below `n`,
    and no duplicates. -/
theorem subsets_valid (n : Nat) : ∀ (s : Nat) (vs : List Nat),
    vs ∈ subsets n s →
    vs.length = s ∧ (∀ v ∈ vs, v < n) ∧ vs.Nodup := by
  induction n with
  | zero =>
    intro s vs hvs
    match s with
    | 0 => simp [subsets] at hvs; subst hvs; exact ⟨rfl, nofun, .nil⟩
    | _ + 1 => simp [subsets] at hvs
  | succ n ih =>
    intro s vs hvs
    match s with
    | 0 => simp [subsets] at hvs; subst hvs; exact ⟨rfl, nofun, .nil⟩
    | s + 1 =>
      simp only [subsets, List.mem_append, List.mem_map] at hvs
      rcases hvs with ⟨tl, htl, rfl⟩ | hvs
      · obtain ⟨hlen, hbound, hnodup⟩ := ih s tl htl
        refine ⟨by simp [hlen], ?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hvtl
          · omega
          · exact Nat.lt_succ_of_lt (hbound v hvtl)
        · rw [List.nodup_cons]
          exact ⟨fun hmem => Nat.lt_irrefl n (hbound n hmem), hnodup⟩
      · obtain ⟨hlen, hbound, hnodup⟩ := ih (s + 1) vs hvs
        exact ⟨hlen, fun v hv => Nat.lt_succ_of_lt (hbound v hv), hnodup⟩

/-- Every clique edge appears among the clique's edge variables. -/
theorem cliqueEdgeVars_complete (n : Nat) (vs : List Nat)
    (i j : Nat) (hi : i ∈ vs) (hj : j ∈ vs) (hij : i < j) :
    edgeVar n i j ∈ cliqueEdgeVars n vs := by
  simp only [cliqueEdgeVars, List.mem_flatMap, List.mem_filterMap]
  exact ⟨i, hi, j, hj, by simp [hij]⟩

/-- A non-red clique has a false edge variable. -/
theorem exists_false_edge (n : Nat) (vs : List Nat) (f : Nat → Bool)
    (h : ¬(∀ i j, i ∈ vs → j ∈ vs → i < j → f (edgeVar n i j) = true)) :
    ∃ v ∈ cliqueEdgeVars n vs, f v = false := by
  have hdiff : ∃ i j, i ∈ vs ∧ j ∈ vs ∧ i < j ∧ f (edgeVar n i j) ≠ true :=
    Classical.byContradiction fun hall =>
      h fun i j hi hj hij =>
        Classical.byContradiction fun hne =>
          hall ⟨i, j, hi, hj, hij, hne⟩
  obtain ⟨i, j, hi, hj, hij, hne⟩ := hdiff
  have hf : f (edgeVar n i j) = false := by
    cases hc : f (edgeVar n i j)
    · rfl
    · exact absurd hc hne
  exact ⟨edgeVar n i j, cliqueEdgeVars_complete n vs i j hi hj hij, hf⟩

/-- A non-blue clique has a true edge variable. -/
theorem exists_true_edge (n : Nat) (vs : List Nat) (f : Nat → Bool)
    (h : ¬(∀ i j, i ∈ vs → j ∈ vs → i < j → f (edgeVar n i j) = false)) :
    ∃ v ∈ cliqueEdgeVars n vs, f v = true := by
  have hdiff : ∃ i j, i ∈ vs ∧ j ∈ vs ∧ i < j ∧ f (edgeVar n i j) ≠ false :=
    Classical.byContradiction fun hall =>
      h fun i j hi hj hij =>
        Classical.byContradiction fun hne =>
          hall ⟨i, j, hi, hj, hij, hne⟩
  obtain ⟨i, j, hi, hj, hij, hne⟩ := hdiff
  have hf : f (edgeVar n i j) = true := by
    cases hc : f (edgeVar n i j)
    · exact absurd hc hne
    · rfl
  exact ⟨edgeVar n i j, cliqueEdgeVars_complete n vs i j hi hj hij, hf⟩

/-- A Ramsey-free coloring satisfies every clause of the encoding. -/
theorem clause_sat_of_mem (n s t : Nat) (f : Nat → Bool)
    (hfree : isRamseyFree n s t f) (cl : CNF.Clause Nat)
    (hcl : cl ∈ (encode n s t).clauses) :
    CNF.Clause.eval f cl = true := by
  obtain ⟨hred, hblue⟩ := hfree
  simp only [encode, List.mem_toArray, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp hcl
    obtain ⟨hlen, hbound, hnodup⟩ := subsets_valid n s vs hvs
    obtain ⟨v, hv, hf⟩ :=
      exists_false_edge n vs f (hred vs hlen hbound hnodup)
    simp only [redClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨v, hv, by simp [Function.comp, hf]⟩
  · obtain ⟨vs, hvs, rfl⟩ := List.mem_map.mp hcl
    obtain ⟨hlen, hbound, hnodup⟩ := subsets_valid n t vs hvs
    obtain ⟨v, hv, hf⟩ :=
      exists_true_edge n vs f (hblue vs hlen hbound hnodup)
    simp only [blueClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨v, hv, by simp [Function.comp, hf]⟩

/-- **Encoding soundness**: if the encoding is UNSAT, every 2-coloring of
    `K_n` contains a red `K_s` or a blue `K_t` — that is, `R(s,t) ≤ n`. -/
theorem no_ramsey_free_of_unsat (n s t : Nat)
    (hunsat : (encode n s t).Unsat) : ¬hasRamseyFreeColoring n s t := by
  intro ⟨f, hfree⟩
  have heval := hunsat f
  rw [CNF.eval, Array.all_eq_false'] at heval
  obtain ⟨cl, hcl, hfalse⟩ := heval
  exact hfalse (clause_sat_of_mem n s t f hfree cl hcl)

/-! ## Witness checking (lower bounds) -/

/-- Decompose a clique edge variable into its endpoints. -/
theorem cliqueEdgeVars_mem (n : Nat) (vs : List Nat) (v : Nat)
    (hv : v ∈ cliqueEdgeVars n vs) :
    ∃ i j, i ∈ vs ∧ j ∈ vs ∧ i < j ∧ v = edgeVar n i j := by
  simp only [cliqueEdgeVars, List.mem_flatMap, List.mem_filterMap] at hv
  obtain ⟨i, hi, j, hj, hcond⟩ := hv
  split at hcond
  · next hij =>
    simp only [Option.some.injEq] at hcond
    exact ⟨i, j, hi, hj, hij, hcond.symm⟩
  · simp at hcond

/-- Every duplicate-free list of vertices below `n` is represented, as a
    set, by some enumerated subset. -/
theorem subsets_complete (n : Nat) : ∀ (s : Nat) (vs : List Nat),
    vs.Nodup → (∀ v ∈ vs, v < n) → vs.length = s →
    ∃ ws ∈ subsets n s, ∀ x, x ∈ ws ↔ x ∈ vs := by
  induction n with
  | zero =>
    intro s vs hnd hb hlen
    match vs with
    | [] => subst hlen; exact ⟨[], by simp [subsets], by simp⟩
    | v :: _ => exact absurd (hb v (.head _)) (Nat.not_lt_zero v)
  | succ n ih =>
    intro s vs hnd hb hlen
    match s with
    | 0 =>
      have hnil := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      exact ⟨[], by simp [subsets], by simp⟩
    | s + 1 =>
      rcases Classical.em (n ∈ vs) with hn | hn
      · -- `n` occurs: recurse on `vs.erase n`, prepend `n`.
        have hb' : ∀ v ∈ vs.erase n, v < n := by
          intro v hv
          have hne : v ≠ n := (hnd.mem_erase_iff.mp hv).1
          have := hb v (List.mem_of_mem_erase hv)
          omega
        have hlen' : (vs.erase n).length = s := by
          rw [List.length_erase_of_mem hn, hlen]; omega
        obtain ⟨ws, hws, hiff⟩ := ih s (vs.erase n) (hnd.erase n) hb' hlen'
        refine ⟨n :: ws, ?_, ?_⟩
        · simp only [subsets, List.mem_append, List.mem_map]
          exact Or.inl ⟨ws, hws, rfl⟩
        · intro x
          simp only [List.mem_cons, hiff x, hnd.mem_erase_iff]
          constructor
          · intro hx
            rcases hx with rfl | ⟨_, hx⟩
            · exact hn
            · exact hx
          · intro hx
            rcases Classical.em (x = n) with rfl | hne
            · exact Or.inl rfl
            · exact Or.inr ⟨hne, hx⟩
      · -- `n` does not occur: `vs` lives below `n`.
        have hb' : ∀ v ∈ vs, v < n := by
          intro v hv
          rcases Classical.em (v = n) with rfl | hne
          · exact absurd hv hn
          · have := hb v hv; omega
        obtain ⟨ws, hws, hiff⟩ := ih (s + 1) vs hnd hb' hlen
        refine ⟨ws, ?_, hiff⟩
        simp only [subsets, List.mem_append]
        exact Or.inr hws

/-- Boolean check that `f` has no red `K_s` and no blue `K_t` on `K_n`. -/
def checkRamseyFree (n s t : Nat) (f : Nat → Bool) : Bool :=
  ((subsets n s).all fun vs => (cliqueEdgeVars n vs).any fun v => !f v) &&
  ((subsets n t).all fun vs => (cliqueEdgeVars n vs).any fun v => f v)

theorem checkRamseyFree_spec (n s t : Nat) (f : Nat → Bool)
    (hcheck : checkRamseyFree n s t f = true) : isRamseyFree n s t f := by
  rw [checkRamseyFree, Bool.and_eq_true] at hcheck
  obtain ⟨hredchk, hbluechk⟩ := hcheck
  rw [List.all_eq_true] at hredchk hbluechk
  constructor
  · intro vs hlen hb hnd hall
    obtain ⟨ws, hws, hiff⟩ := subsets_complete n s vs hnd hb hlen
    have hany := hredchk ws hws
    rw [List.any_eq_true] at hany
    obtain ⟨v, hv, hfv⟩ := hany
    obtain ⟨i, j, hi, hj, hij, rfl⟩ := cliqueEdgeVars_mem n ws v hv
    have := hall i j ((hiff i).mp hi) ((hiff j).mp hj) hij
    simp [this] at hfv
  · intro vs hlen hb hnd hall
    obtain ⟨ws, hws, hiff⟩ := subsets_complete n t vs hnd hb hlen
    have hany := hbluechk ws hws
    rw [List.any_eq_true] at hany
    obtain ⟨v, hv, hfv⟩ := hany
    obtain ⟨i, j, hi, hj, hij, rfl⟩ := cliqueEdgeVars_mem n ws v hv
    have := hall i j ((hiff i).mp hi) ((hiff j).mp hj) hij
    simp [this] at hfv

/-- Lower-bound witness: a checked coloring shows `hasRamseyFreeColoring`. -/
theorem witness_ramsey_free (n s t : Nat) (f : Nat → Bool)
    (hcheck : checkRamseyFree n s t f = true) : hasRamseyFreeColoring n s t :=
  ⟨f, checkRamseyFree_spec n s t f hcheck⟩

/-- `R(s,t) = n`: `K_{n-1}` admits a coloring with no red `K_s` and no blue
    `K_t`, but `K_n` does not. -/
def ramseyNumber (s t n : Nat) : Prop :=
  hasRamseyFreeColoring (n - 1) s t ∧ ¬hasRamseyFreeColoring n s t

/-! ## Command -/

/-- `ramsey_lrat name n s t "proof.lrat"`: registers
    `name : ¬ hasRamseyFreeColoring n s t` (the upper bound `R(s,t) ≤ n`)
    from an LRAT refutation of `encode n s t` (DIMACS file via
    `lratcatch-gen ramsey n s t out.cnf`). -/
elab "ramsey_lrat " nm:ident ppSpace nTerm:num ppSpace sTerm:num
    ppSpace tTerm:num ppSpace lratFile:str : command => do
  let lratStr ← LRATCatcher.readFile' lratFile.getString
  if let .error e := Std.Tactic.BVDecide.LRAT.parseLRATProof lratStr.toUTF8 then
    throwError "ramsey_lrat: LRAT parse error in '{lratFile.getString}': {e}"
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (← `(command|
    theorem $nm : ¬ LRATCatcher.Ramsey.hasRamseyFreeColoring $nTerm $sTerm $tTerm :=
      LRATCatcher.Ramsey.no_ramsey_free_of_unsat $nTerm $sTerm $tTerm
        (LRATCatcher.checkLratCnf_sound (LRATCatcher.Ramsey.encode $nTerm $sTerm $tTerm)
          $lratLit (by native_decide))))

end LRATCatcher.Ramsey
