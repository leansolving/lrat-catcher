import LRATCatcher.Cover

/-!
  Tests for the elaboration-time DIMACS and iCNF validators
  (`validateDimacs`, `validateICnf`).
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

-- A clause line with a non-integer token is rejected (here a `c` in mid-line,
-- which `parseDimacs` would skip, reading `1 0 -1 0` as two clauses).
/-- error: midline.cnf:2: non-integer token 'c' in clause line -/
#guard_msgs in
run_cmd validateDimacs "midline.cnf" "p cnf 1 1\n1 0 c -1 0\n"

-- `toInt?` accepts `_` digit separators; DIMACS does not.
/-- error: underscore.cnf:2: non-integer token '1_0' in clause line -/
#guard_msgs in
run_cmd validateDimacs "underscore.cnf" "p cnf 10 1\n1_0 0\n"

-- A `p` line that is not `p cnf <n> <m>` is rejected.
/-- error: header.cnf:1: malformed header (expected 'p cnf <vars> <clauses>'): 'p garbage' -/
#guard_msgs in
run_cmd validateDimacs "header.cnf" "p garbage\n1 0\n"

/-- error: header2.cnf:1: malformed header (expected 'p cnf <vars> <clauses>'): 'p cnf 1' -/
#guard_msgs in
run_cmd validateDimacs "header2.cnf" "p cnf 1\n1 0\n"

-- Counts that disagree with the header give warnings, not errors.
/--
warning: counts.cnf: variable 3 exceeds the 1 variables declared in the header
---
warning: counts.cnf: 1 clauses, but the header declares 99
-/
#guard_msgs in
run_cmd validateDimacs "counts.cnf" "p cnf 1 99\n1 -3 0\n"

-- An empty clause gives a warning: at the start of the file, after a `0`, and
-- on its own line; none for a file without one.
/-- warning: empty1.cnf: contains an empty clause — the CNF is trivially unsatisfiable -/
#guard_msgs in
run_cmd validateDimacs "empty1.cnf" "p cnf 1 2\n0\n1 0\n"

/-- warning: empty2.cnf: contains an empty clause — the CNF is trivially unsatisfiable -/
#guard_msgs in
run_cmd validateDimacs "empty2.cnf" "p cnf 1 2\n1 0 0\n"

/-- warning: empty3.cnf: contains an empty clause — the CNF is trivially unsatisfiable -/
#guard_msgs in
run_cmd validateDimacs "empty3.cnf" "1 0\n0\n-1 0\n"

#guard_msgs in
run_cmd validateDimacs "noempty.cnf" "p cnf 2 2\n1 2 0\n-1\n-2 0\n"

#guard (parseDimacs "p cnf 1 2\n1 0 0\n").clauses.any (·.size == 0)
#guard !(parseDimacs "p cnf 2 2\n1 2 0\n-1\n-2 0\n").clauses.any (·.size == 0)

-- The iCNF validator: `p inccnf` header, `_` rejected, empty cube warned.
#guard_msgs in
run_cmd validateICnf "ok.icnf" "p inccnf\na 1 -2 0\na -1 0\n"

/-- error: hdr.icnf:1: malformed header (expected 'p inccnf'): 'p cnf 2 2' -/
#guard_msgs in
run_cmd validateICnf "hdr.icnf" "p cnf 2 2\na 1 0\n"

/-- error: us.icnf:1: non-integer token '1_0' in cube line -/
#guard_msgs in
run_cmd validateICnf "us.icnf" "a 1_0 0\n"

/-- warning: e.icnf:1: empty cube 'a 0' — this leaf equals the base formula -/
#guard_msgs in
run_cmd validateICnf "e.icnf" "a 0\n"

end LRATCatcher.Tests
