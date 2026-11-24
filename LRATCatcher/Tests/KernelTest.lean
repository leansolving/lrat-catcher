import LRATCatcher.Reflect

/-!
  Tests for kernel-mode reflection (`+kernel` variants of the commands).
  The `#print axioms` lines document the trust dial: kernel-mode theorems
  depend only on the standard axioms (propext, Classical.choice, Quot.sound) —
  no per-theorem `native_decide` axiom, i.e. no compiler trust.
-/

namespace LRATCatcher.Tests

-- File form: statement is about the embedded CNF literal.
lrat_reflect +kernel tiny_kernel "LRATCatcher/Tests/tiny.cnf" "LRATCatcher/Tests/tiny.lrat"

#print axioms tiny_kernel

-- Lean-defined CNF form (mirrors ReflectTest.tinyDef).
def tinyDefK : Std.Sat.CNF Nat :=
  { clauses := #[.ofLiterals [(0, true), (1, true)], .ofLiterals [(0, false), (1, true)],
                 .ofLiterals [(0, true), (1, false)], .ofLiterals [(0, false), (1, false)]] }

lrat_reflect_cnf +kernel tiny_def_kernel (tinyDefK) "LRATCatcher/Tests/tiny.lrat"

#print axioms tiny_def_kernel

-- A PHP(4,3) cube leaf, checked in kernel mode.
lrat_reflect +kernel php43_leaf1_kernel "examples/php43/leaf1.cnf" "examples/php43/leaf1.lrat"

#print axioms php43_leaf1_kernel

/-! The kernel checker accepts some certificates the core checker rejects.
  Clauses `x`, `x ∨ ¬x`, `¬x` and one empty-clause step with hints 1, 2, 3:
  the kernel checker propagates `x` from hint 2 (its literal `¬x` is false
  after hint 1); core propagation returns an error on a hint clause with an
  atom in both polarities. -/
def tautHintCnf : Std.Sat.CNF Nat :=
  { clauses := #[.ofLiterals [(0, true)], .ofLiterals [(0, true), (0, false)],
                 .ofLiterals [(0, false)]] }

def tautHintProof : List Std.Tactic.BVDecide.LRAT.IntAction := [.addEmpty 4 #[1, 2, 3]]

#guard checkKernel tautHintCnf tautHintProof
#guard Std.Tactic.BVDecide.LRAT.check tautHintProof.toArray tautHintCnf = false

example : checkKernel tautHintCnf tautHintProof = true := by decide +kernel

-- Without the tautological hint both checkers accept.
#guard checkKernel tautHintCnf [.addEmpty 4 #[1, 3]]
#guard Std.Tactic.BVDecide.LRAT.check #[.addEmpty 4 #[1, 3]] tautHintCnf

end LRATCatcher.Tests
