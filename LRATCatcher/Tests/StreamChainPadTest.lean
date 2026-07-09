import LRATCatcher.Stream

/-!
  StreamChainPadTest — chained streaming derivations with a padding tautology.

  A single streamed derivation embeds its base from a DIMACS file. To *chain*
  derivations (as a chained presolve pipeline does — batch `i+1`'s base is batch `i`'s
  *derived* formula plus a fresh padding clause), the base of a later batch must
  be a Lean **term**, not a file. Two library pieces make this compose:

  * `padCNF v` — the one-clause tautology `[v ∨ ¬v]`, satisfied by every
    assignment;
  * `unsat_of_append_pad` — peels the padding clause off a refutation.

  This test builds a genuine two-stage chain with tiny hand-written RUP
  derivations (no solver needed), mirroring exactly what

      lratcatch-stream-gen derive examples/chainpad/f0.cnf \
          examples/chainpad/deriv0.lrat ChainPadA 1
      lratcatch-stream-gen derive <ChainPadA fprime.cnf> \
          examples/chainpad/deriv1.lrat ChainPadB 1 \
          --pad 3 --chain-prev LRATCatcher.Generated.ChainPadA.Snap1 snap1

  emits, but self-contained (the generated modules live under the gitignored
  `LRATCatcher/Generated/`). Stages:

  * stage A: `f0` (a file) ⊢ `f0 ∪ {(2)}` (its derived formula = `externSnap snapA`);
  * stage B: base `= externSnap snapA ++ padCNF 3` (a *term*) ⊢ one more clause.

  `derivB'` peels the pad so it targets the *unpadded* stage-A derived formula,
  and composing with `derivA` transfers a refutation of stage B's derived
  formula down to the original `f0`.

  Trust base (see `#print axioms`): the standard axioms + one `native_decide`
  axiom per stage; `padCNF_eval`/`unsat_of_append_pad` add none.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT LRATCatcher

namespace LRATCatcher.Tests.StreamChainPadTest

/-! ## Unit tests for the padding lemmas -/

-- The padding clause is a tautology: true under every assignment.
example (a : Nat → Bool) : CNF.eval a (padCNF 7) = true := padCNF_eval a 7
#guard CNF.eval (fun _ => false) (padCNF 5)
#guard CNF.eval (fun _ => true) (padCNF 5)

-- Peeling the pad off a refutation.
example {F : CNF Nat} (h : (F ++ padCNF 9).Unsat) : F.Unsat := unsat_of_append_pad h

/-! ## Stage A: `f0` ⊢ `f0 ∪ {(2)}` -/

/-- `f0`: unsatisfiable over two variables. -/
def f0 : String := "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
def baseA : CNF Nat := parseDimacs f0
/-- Snapshot after stage A's single chunk: `f0`'s clauses plus the derived `(2)`. -/
def snapA : Snapshot := parseSnap ".\n2 1 0\n2 -1 0\n-2 1 0\n-2 -1 0\n2 0\n"

-- Derive `(2)` by RUP: assume `¬2`; clause 1 `(1∨2)` gives `1`; clause 2
-- `(¬1∨2)` then conflicts. Hints `[1, 2]`.
theorem stepA : stepStart baseA (parseActions "5 2 0 1 2 0\n") snapA = true := by
  native_decide

/-- Stage A derivation: refuting `externSnap snapA` refutes `f0`. -/
theorem derivA (hx : (externSnap snapA).Unsat) : baseA.Unsat :=
  stepStart_extern stepA hx

/-! ## Stage B: `externSnap snapA ++ padCNF 3` ⊢ … (base is a term) -/

/-- Batch B's base: stage A's derived formula plus a fresh padding clause
    `[3 ∨ ¬3]` (clause id 6). A Lean term — no file string embedded. -/
def baseB : CNF Nat := externSnap snapA ++ padCNF 3
/-- Snapshot after stage B's single chunk: `baseB` (minus tautology holes) plus `(1)`. -/
def snapB : Snapshot := parseSnap ".\n2 1 0\n2 -1 0\n-2 1 0\n-2 -1 0\n2 0\n1 0\n"

-- Derive `(1)` by RUP against `baseB`: assume `¬1`; clause 3 `(¬2∨1)` gives
-- `¬2`; clause 5 `(2)` then conflicts. Hints `[3, 5]`.
theorem stepB : stepStart baseB (parseActions "7 1 0 3 5 0\n") snapB = true := by
  native_decide

/-- Stage B derivation: refuting `externSnap snapB` refutes the padded base. -/
theorem derivB (hx : (externSnap snapB).Unsat) : baseB.Unsat :=
  stepStart_extern stepB hx

/-- Pad peeled off: refuting `externSnap snapB` refutes the *unpadded* stage-A
    derived formula `externSnap snapA`. -/
theorem derivB' (hx : (externSnap snapB).Unsat) : (externSnap snapA).Unsat :=
  unsat_of_append_pad (derivB hx)

/-! ## Composition -/

/-- Two-stage chain composed: a refutation of stage B's derived formula
    transfers all the way down to the original `f0`. -/
theorem f0_of_chainB_unsat (hx : (externSnap snapB).Unsat) : baseA.Unsat :=
  derivA (derivB' hx)

#print axioms f0_of_chainB_unsat

end LRATCatcher.Tests.StreamChainPadTest
