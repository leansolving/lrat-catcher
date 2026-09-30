import LRATCatcher.Reflect

/-!
  Tests for the elaboration-time DIMACS validator `validateDimacs`.
-/

namespace LRATCatcher.Tests

-- A file without clauses is valid DIMACS; `parseDimacs` reads it as the empty CNF.
run_cmd validateDimacs "empty3.cnf" "p cnf 3 0\n"
run_cmd validateDimacs "empty3_nonl.cnf" "p cnf 3 0"
run_cmd validateDimacs "empty0.cnf" "p cnf 0 0\n"
run_cmd validateDimacs "empty_comments.cnf" "c header-only file\np cnf 3 0\nc trailing comment\n"

#guard (parseDimacs "p cnf 3 0\n").clauses.isEmpty

-- An unterminated final clause is still rejected.
/-- error: unterminated.cnf: final clause is not terminated by 0 -/
#guard_msgs in
run_cmd validateDimacs "unterminated.cnf" "p cnf 2 2\n1 2 0\n-1 2\n"

/-- error: unterminated1.cnf: final clause is not terminated by 0 -/
#guard_msgs in
run_cmd validateDimacs "unterminated1.cnf" "p cnf 2 1\n1 2"

end LRATCatcher.Tests
