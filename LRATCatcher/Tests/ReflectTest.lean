import LRATCatcher.Reflect

/-!
  Tests for the `lrat_reflect` / `lrat_reflect_cnf` commands on the tiny instance.
-/

namespace LRATCatcher.Tests

-- Standalone DIMACS + LRAT import.
lrat_reflect tiny_cmd "LRATCatcher/Tests/tiny.cnf" "LRATCatcher/Tests/tiny.lrat"

#print axioms tiny_cmd

-- Lean-defined CNF + LRAT certificate (verified-encoding form).
def tinyDef : Std.Sat.CNF Nat :=
  { clauses := #[[(0, true), (1, true)], [(0, false), (1, true)],
                 [(0, true), (1, false)], [(0, false), (1, false)]] }

lrat_reflect_cnf tiny_def_cmd (tinyDef) "LRATCatcher/Tests/tiny.lrat"

#print axioms tiny_def_cmd

end LRATCatcher.Tests
