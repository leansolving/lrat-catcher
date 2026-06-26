import LRATLean.Reflect

/-!
  # Verified Schur encoding

  End-to-end verified Schur bounds: Lean encodes k-coloring Schur-freeness of
  `{1,…,n}` as a CNF, an external SAT solver refutes it, and the LRAT
  certificate yields `¬ hasKSchurFreeColoring k n` — a statement about
  colorings, not about CNF.

  A k-coloring of `{1,…,n}` is *Schur-free* if no triple `(a, b, a+b)` is
  monochromatic. The Schur number `S(k)` is the largest `n` admitting a
  Schur-free k-coloring; `¬ hasKSchurFreeColoring k (S(k)+1)` is the upper
  bound, certified here; the lower bound is an explicit witness coloring
  checked by `native_decide`.

  Encoding (variables `kVar k i c = (i-1)·k + c`, "element i has color c"):
  * at-least-one color per element (k-literal clause);
  * for each Schur triple and color, not-all-three (3-literal clause).
  At-most-one constraints are unnecessary: any satisfying assignment yields a
  coloring by picking the least asserted color, and a Schur-free coloring
  satisfies the encoding, which is the direction soundness needs.

  The DIMACS file for the solver is produced by `lratlean-gen schur k n out`
  from the *same* `encodeK` function, so the certified CNF and the solved CNF
  coincide by construction.
-/

open Lean Elab Command
open Std.Sat

namespace LRATLean.Schur

/-! ## Triples and encoding -/

/-- Schur triples `(a, b, a+b)` with `1 ≤ a ≤ b`, `a+b ≤ n`. -/
def schurTriples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a0 =>
    (List.range n).filterMap fun b0 =>
      let a := a0 + 1
      let b := b0 + 1
      if a ≤ b && a + b ≤ n then some (a, b, a + b) else none

/-- Variable index for "element i has color c" (i 1-based, c 0-based). -/
def kVar (k i c : Nat) : Nat := (i - 1) * k + c

/-- At-least-one-color clause for element `i`. -/
def aloClause (k i : Nat) : CNF.Clause Nat :=
  (List.range k).map fun c => (kVar k i c, true)

/-- Not-all-three clause for triple `(a, b, c)` and color `col`. -/
def monoClause (k a b c col : Nat) : CNF.Clause Nat :=
  [(kVar k a col, false), (kVar k b col, false), (kVar k c col, false)]

/-- CNF encoding of "`{1,…,n}` has a Schur-free k-coloring". -/
def encodeK (k n : Nat) : CNF Nat :=
  let alo := (List.range n).map fun i0 => aloClause k (i0 + 1)
  let mono := (schurTriples n).flatMap fun (a, b, c) =>
    (List.range k).map fun col => monoClause k a b c col
  { clauses := (alo ++ mono).toArray }

/-! ## Mathematical predicates -/

/-- `f` is a Schur-free k-coloring of `{1,…,n}`. -/
def isKSchurFree (k n : Nat) (f : Nat → Nat) : Prop :=
  (∀ i, 1 ≤ i → i ≤ n → f i < k) ∧
  (∀ a b : Nat, 1 ≤ a → a ≤ b → a + b ≤ n →
    ¬(f a = f b ∧ f b = f (a + b)))

/-- `{1,…,n}` admits a Schur-free k-coloring. -/
def hasKSchurFreeColoring (k n : Nat) : Prop :=
  ∃ f : Nat → Nat, isKSchurFree k n f

/-! ## Encoding soundness -/

/-- The valuation induced by a coloring. -/
def kColoringVal (k : Nat) (f : Nat → Nat) (v : Nat) : Bool :=
  f (v / k + 1) == (v % k)

theorem kColoringVal_eq (k : Nat) (f : Nat → Nat) (i c : Nat)
    (hk : 0 < k) (hi : 1 ≤ i) (hc : c < k) :
    kColoringVal k f (kVar k i c) = (f i == c) := by
  simp only [kColoringVal, kVar]
  have hmod : ((i - 1) * k + c) % k = c := by
    rw [show (i - 1) * k + c = c + (i - 1) * k by omega]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hdiv : ((i - 1) * k + c) / k = i - 1 := by
    rw [show (i - 1) * k + c = c + (i - 1) * k by omega]
    rw [Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hc, Nat.zero_add]
  simp [hmod, hdiv, show i - 1 + 1 = i by omega]

theorem alo_sat (k n : Nat) (f : Nat → Nat) (i : Nat)
    (hk : 0 < k) (hi : 1 ≤ i) (hin : i ≤ n) (hcol : ∀ j, 1 ≤ j → j ≤ n → f j < k) :
    CNF.Clause.eval (kColoringVal k f) (aloClause k i) = true := by
  have hfi := hcol i hi hin
  simp only [aloClause, CNF.Clause.eval, List.any_map, List.any_eq_true]
  refine ⟨f i, List.mem_range.mpr hfi, ?_⟩
  simp [Function.comp, kColoringVal_eq k f i (f i) hk hi hfi]

theorem mono_sat (k n : Nat) (f : Nat → Nat) (a b c col : Nat)
    (hk : 0 < k) (ha : 1 ≤ a) (hab : a ≤ b) (hle : a + b ≤ n) (hc : c = a + b)
    (hcol : col < k)
    (hfree : ∀ a' b' : Nat, 1 ≤ a' → a' ≤ b' → a' + b' ≤ n →
      ¬(f a' = f b' ∧ f b' = f (a' + b'))) :
    CNF.Clause.eval (kColoringVal k f) (monoClause k a b c col) = true := by
  simp only [monoClause, CNF.Clause.eval, List.any_cons, List.any_nil,
    Bool.or_false, Bool.or_eq_true,
    kColoringVal_eq k f a col hk ha hcol,
    kColoringVal_eq k f b col hk (by omega) hcol,
    kColoringVal_eq k f c col hk (by omega) hcol]
  -- Direct case analysis: a non-matching color satisfies its literal;
  -- all three matching contradicts Schur-freeness (Mathlib-free, no push_neg).
  cases hfa : f a == col with
  | false => exact Or.inl rfl
  | true =>
    cases hfb : f b == col with
    | false => exact Or.inr (Or.inl rfl)
    | true =>
      cases hfc : f c == col with
      | false => exact Or.inr (Or.inr rfl)
      | true =>
        have ea := beq_iff_eq.mp hfa
        have eb := beq_iff_eq.mp hfb
        have ec := beq_iff_eq.mp hfc
        exact absurd ⟨ea.trans eb.symm, eb.trans (hc ▸ ec).symm⟩
          (hfree a b ha hab hle)

/-- A Schur-free coloring satisfies every clause of the encoding. -/
theorem clause_sat_of_mem (k n : Nat) (f : Nat → Nat) (hk : 0 < k)
    (hfree : isKSchurFree k n f) (cl : CNF.Clause Nat)
    (hcl : cl ∈ (encodeK k n).clauses) :
    CNF.Clause.eval (kColoringVal k f) cl = true := by
  obtain ⟨hcol, htriple⟩ := hfree
  simp only [encodeK, List.mem_toArray, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hcl
    exact alo_sat k n f (i0 + 1) hk (by omega) (by
      have := List.mem_range.mp hi0; omega) hcol
  · simp only [List.mem_flatMap] at hcl
    obtain ⟨⟨a, b, c⟩, htri, hcl⟩ := hcl
    obtain ⟨col, hcol_mem, rfl⟩ := List.mem_map.mp hcl
    have hcol_lt := List.mem_range.mp hcol_mem
    have ⟨ha, hab, hle, hc⟩ : 1 ≤ a ∧ a ≤ b ∧ a + b ≤ n ∧ c = a + b := by
      simp only [schurTriples, List.mem_flatMap, List.mem_range,
        List.mem_filterMap] at htri
      obtain ⟨a0, _, b0, _, hcond⟩ := htri
      split at hcond
      · next hgood =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hcond
        obtain ⟨rfl, rfl, rfl⟩ := hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hgood
        exact ⟨by omega, hgood.1, hgood.2, rfl⟩
      · simp at hcond
    exact mono_sat k n f a b c col hk ha hab hle hc hcol_lt htriple

/-- **Encoding soundness**: if the encoding is UNSAT, no Schur-free
    k-coloring of `{1,…,n}` exists. -/
theorem no_k_schur_free_of_unsat (k n : Nat) (hk : 0 < k)
    (hunsat : (encodeK k n).Unsat) : ¬hasKSchurFreeColoring k n := by
  intro ⟨f, hfree⟩
  have heval := hunsat (kColoringVal k f)
  rw [CNF.eval, Array.all_eq_false'] at heval
  obtain ⟨cl, hcl, hfalse⟩ := heval
  exact hfalse (clause_sat_of_mem k n f hk hfree cl hcl)

/-! ## Witness checking (lower bounds) -/

/-- Boolean check that `f` is a Schur-free k-coloring of `{1,…,n}`. -/
def checkKSchurFree (k n : Nat) (f : Nat → Nat) : Bool :=
  ((List.range n).all fun i0 => f (i0 + 1) < k) &&
  ((schurTriples n).all fun (a, b, c) => !(f a == f b && f b == f c))

theorem checkKSchurFree_spec (k n : Nat) (f : Nat → Nat)
    (hcheck : checkKSchurFree k n f = true) : isKSchurFree k n f := by
  rw [checkKSchurFree, Bool.and_eq_true] at hcheck
  obtain ⟨hcol, htri⟩ := hcheck
  constructor
  · intro i hi hin
    rw [List.all_eq_true] at hcol
    have := hcol (i - 1) (List.mem_range.mpr (by omega))
    simpa [show i - 1 + 1 = i by omega] using this
  · intro a b ha hab hle ⟨h1, h2⟩
    rw [List.all_eq_true] at htri
    have hmem : (a, b, a + b) ∈ schurTriples n := by
      simp only [schurTriples, List.mem_flatMap, List.mem_range,
        List.mem_filterMap]
      exact ⟨a - 1, by omega, b - 1, by omega,
        by simp [show a - 1 + 1 = a by omega,
                 show b - 1 + 1 = b by omega, hab, hle]⟩
    have := htri (a, b, a + b) hmem
    simp [h1, h2] at this

/-- Lower-bound witness: a checked coloring shows `hasKSchurFreeColoring`. -/
theorem witness_k_schur_free (k n : Nat) (f : Nat → Nat)
    (hcheck : checkKSchurFree k n f = true) : hasKSchurFreeColoring k n :=
  ⟨f, checkKSchurFree_spec k n f hcheck⟩

/-- `S(k) = n`: `{1,…,n}` admits a Schur-free k-coloring but `{1,…,n+1}`
    does not. -/
def schurNumber (k n : Nat) : Prop :=
  hasKSchurFreeColoring k n ∧ ¬hasKSchurFreeColoring k (n + 1)

/-! ## Command -/

/-- `schur_lrat name k n "proof.lrat"`: registers
    `name : ¬ hasKSchurFreeColoring k n` from an LRAT refutation of
    `encodeK k n` (DIMACS file via `lratlean-gen schur k n out.cnf`). -/
elab "schur_lrat " nm:ident ppSpace kTerm:num ppSpace nTerm:num
    ppSpace lratFile:str : command => do
  if kTerm.getNat == 0 then
    throwError "schur_lrat: k must be positive"
  let lratStr ← LRATLean.readFile' lratFile.getString
  if let .error e := Std.Tactic.BVDecide.LRAT.parseLRATProof lratStr.toUTF8 then
    throwError "schur_lrat: LRAT parse error in '{lratFile.getString}': {e}"
  let lratLit := Syntax.mkStrLit lratStr
  elabCommand (← `(command|
    theorem $nm : ¬ LRATLean.Schur.hasKSchurFreeColoring $kTerm $nTerm :=
      LRATLean.Schur.no_k_schur_free_of_unsat $kTerm $nTerm (by omega)
        (LRATLean.checkLratCnf_sound (LRATLean.Schur.encodeK $kTerm $nTerm)
          $lratLit (by native_decide))))

end LRATLean.Schur
