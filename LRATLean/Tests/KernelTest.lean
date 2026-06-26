import LRATLean.Reflect

/-!
  Tests for kernel-mode reflection (`+kernel` variants of the commands).
  The `#print axioms` lines document the trust dial: kernel-mode theorems
  depend only on the standard axioms (propext, Classical.choice, Quot.sound) —
  no per-theorem `native_decide` axiom, i.e. no compiler trust.
-/

namespace LRATLean.Tests

-- File form: statement is about the embedded CNF literal.
lrat_reflect +kernel tiny_kernel "LRATLean/Tests/tiny.cnf" "LRATLean/Tests/tiny.lrat"

#print axioms tiny_kernel

-- Lean-defined CNF form (mirrors ReflectTest.tinyDef).
def tinyDefK : Std.Sat.CNF Nat :=
  { clauses := #[[(0, true), (1, true)], [(0, false), (1, true)],
                 [(0, true), (1, false)], [(0, false), (1, false)]] }

lrat_reflect_cnf +kernel tiny_def_kernel (tinyDefK) "LRATLean/Tests/tiny.lrat"

#print axioms tiny_def_kernel

-- A PHP(4,3) cube leaf, checked in kernel mode.
lrat_reflect +kernel php43_leaf1_kernel "examples/php43/leaf1.cnf" "examples/php43/leaf1.lrat"

#print axioms php43_leaf1_kernel

end LRATLean.Tests
