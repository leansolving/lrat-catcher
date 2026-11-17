import LRATCatcher.Stream

/-!
  StreamChainPadTest — chained streaming derivations, and why they need no padding.

  A single streamed derivation embeds its base from a DIMACS file. To *chain*
  derivations (as a chained presolve pipeline does — batch `i+1`'s base is batch
  `i`'s *derived* formula), the base of a later batch must be a Lean **term**, not
  a file: `externSnap` of the previous batch's last snapshot.

  This test builds a genuine two-stage chain with tiny hand-written RUP
  derivations (no solver needed), mirroring exactly what

      lratcatch-stream-gen derive examples/chainpad/f0.cnf \
          examples/chainpad/deriv0.lrat ChainPadA 1
      lratcatch-stream-gen derive <ChainPadA fprime.cnf> \
          examples/chainpad/deriv1.lrat ChainPadB 2 \
          --chain-prev LRATCatcher.Generated.ChainPadA.Snap1 snap1

  emits, but self-contained (the generated modules live under the gitignored
  `LRATCatcher/Generated/`). Stages:

  * stage A: `f0` (a file) ⊢ `f0 ∪ {(2)}` (its derived formula = `externSnap snapA`);
  * stage B: base `= externSnap snapA` (a *term*) ⊢ `(1)`, then `(1 ∨ 3)` over the
    fresh variable 3, with a hint naming the clause added in stage B (id 6).

  Composing `derivB` with `derivA` transfers a refutation of stage B's derived
  formula down to the original `f0`.

  Padding. Earlier Lean versions bounded the variables of the LRAT checker, so a
  chained batch whose certificate introduced a fresh variable had its base
  padded with a tautology `[v ∨ ¬v]` on that variable (`padCNF v`), and the
  padding clause had no clause id. The checker of this toolchain has no
  variable bound, so stage B introduces variable 3 without padding; and since
  clause ids are push positions, a padding clause would take id 6 and shift
  every added clause. The negative control below checks that stage B's
  certificate is rejected against the padded base `externSnap snapA ++ padCNF 2`
  (the hint `6` then names the tautology). `lratcatch-stream-gen` refuses
  `--pad` for this reason. `padCNF_eval` and `unsat_of_append_pad` stay in the
  library and keep their unit tests.

  Trust base (see `#print axioms`): the standard axioms + one `native_decide`
  axiom per stage.
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
def snapA : Snapshot := parseSnap ".\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n2 0\n"

-- Derive `(2)` by RUP: assume `¬2`; clause 1 `(1∨2)` gives `1`; clause 2
-- `(¬1∨2)` then conflicts. Hints `[1, 2]`.
theorem stepA : stepStart baseA (parseActions "5 2 0 1 2 0\n") snapA = true := by
  native_decide

/-- Stage A derivation: refuting `externSnap snapA` refutes `f0`. -/
theorem derivA (hx : (externSnap snapA).Unsat) : baseA.Unsat :=
  stepStart_extern stepA hx

/-! ## Stage B: `externSnap snapA` ⊢ `(1)`, `(1 ∨ 3)` (base is a term) -/

/-- Batch B's base: stage A's derived formula, a Lean term (no file string
    embedded). Its five clauses keep their ids 1-5. -/
def baseB : CNF Nat := externSnap snapA
/-- Stage B's certificate (`examples/chainpad/deriv1.lrat`). -/
def certB : String := "6 1 0 3 5 0\n7 1 3 0 6 0\n"
/-- Snapshot after stage B's single chunk: `baseB` plus `(1)` (id 6) and
    `(1 ∨ 3)` (id 7). -/
def snapB : Snapshot := parseSnap ".\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n2 0\n1 0\n1 3 0\n"

-- Derive `(1)` by RUP against `baseB`: assume `¬1`; clause 3 `(1∨¬2)` gives
-- `¬2`; clause 5 `(2)` then conflicts. Hints `[3, 5]`. Then `(1 ∨ 3)`: assume
-- `¬1, ¬3`; clause 6 `(1)` conflicts. Hint `[6]`.
theorem stepB : stepStart baseB (parseActions certB) snapB = true := by
  native_decide

/-- Stage B derivation: refuting `externSnap snapB` refutes stage A's derived
    formula `externSnap snapA`. -/
theorem derivB (hx : (externSnap snapB).Unsat) : (externSnap snapA).Unsat :=
  stepStart_extern stepB hx

-- Negative control: against the padded base the padding clause takes id 6, so
-- `(1)` lands at id 7 and the hint `6` of the second step names the tautology
-- `[3 ∨ ¬3]`, which is not falsified under `¬1, ¬3`: the chunk is rejected.
#guard (runChunk (.ofCNF (externSnap snapA ++ padCNF 2)) (parseActions certB) 0).isNone
-- The same certificate against the unpadded base is accepted.
#guard (runChunk (.ofCNF baseB) (parseActions certB) 0).isSome

/-! ## Composition -/

/-- Two-stage chain composed: a refutation of stage B's derived formula
    transfers all the way down to the original `f0`. -/
theorem f0_of_chainB_unsat (hx : (externSnap snapB).Unsat) : baseA.Unsat :=
  derivA (derivB hx)

#print axioms f0_of_chainB_unsat

end LRATCatcher.Tests.StreamChainPadTest
