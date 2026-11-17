import LRATCatcher.Reflect

/-!
  `lrat_decide`: the solver is invoked at elaboration time (the CaDiCaL
  bundled with the Lean toolchain, or `LRATCATCHER_SOLVER`; flags `--lrat`
  only, see `solverAndFlags`).
  Instance: the R(3,3) ≤ 6 encoding (instant). Native mode carries the
  per-theorem `native_decide` axiom; kernel mode standard axioms only.
-/

namespace LRATCatcher.Tests

lrat_decide r33Decide "examples/ramsey/r33_6.cnf"

#print axioms r33Decide

lrat_decide +kernel r33DecideKernel "examples/ramsey/r33_6.cnf"

#print axioms r33DecideKernel

end LRATCatcher.Tests
