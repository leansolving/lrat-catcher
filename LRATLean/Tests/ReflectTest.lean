import LRATLean.Reflect

/-!
  Tests for the `lrat_reflect` / `lrat_reflect_cnf` commands on the tiny instance.
-/

namespace LRATLean.Tests

-- Standalone DIMACS + LRAT import.
lrat_reflect tiny_cmd "LRATLean/Tests/tiny.cnf" "LRATLean/Tests/tiny.lrat"

#print axioms tiny_cmd

-- Lean-defined CNF + LRAT certificate (verified-encoding form).
def tinyDef : Std.Sat.CNF Nat :=
  { clauses := #[[(0, true), (1, true)], [(0, false), (1, true)],
                 [(0, true), (1, false)], [(0, false), (1, false)]] }

lrat_reflect_cnf tiny_def_cmd (tinyDef) "LRATLean/Tests/tiny.lrat"

#print axioms tiny_def_cmd

end LRATLean.Tests
