import LRATCatcher.Reflect

/-!
  Scale test: PHP(10,9) — the pigeonhole principle for 10 pigeons and 9
  holes, the canonical resolution-hard family. The 4 KB CNF (90 vars, 415
  clauses) has an LRAT refutation of ~63 MB, which `lrat_decide` produces
  with the build-time solver and imports through the compiled core checker
  in one command. Mathlib's `lrat_proof` (explicit proof terms) is
  impractical at this certificate size: building explicit proof terms exhausts
  memory well before this point.
-/

namespace LRATCatcher.Tests

lrat_decide php109_unsat "examples/php109.cnf"

#print axioms php109_unsat

end LRATCatcher.Tests
