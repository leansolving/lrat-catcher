import LRATCatcher.Reflect

/-!
  `lrat_decide`: the solver is invoked at elaboration time (the CaDiCaL
  bundled with the Lean toolchain, or `LRATCATCHER_SOLVER`; `--no-factor`
  added for cadical ≥ 3 automatically).
  Instance: the R(3,3) ≤ 6 encoding (instant). Native mode carries the
  per-theorem `native_decide` axiom; kernel mode standard axioms only.
-/

namespace LRATCatcher.Tests

lrat_decide r33Decide "examples/ramsey/r33_6.cnf"

#print axioms r33Decide

/- PORT (v4.36.0): kernel mode disabled until the list-based kernel checker exists
lrat_decide +kernel r33DecideKernel "examples/ramsey/r33_6.cnf"

#print axioms r33DecideKernel
-/

end LRATCatcher.Tests
