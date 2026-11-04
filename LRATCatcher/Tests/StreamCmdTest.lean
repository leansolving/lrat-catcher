import LRATCatcher.StreamOracle

/-!
  StreamCmdTest — the `lrat_stream` command end-to-end: cadical is launched
  at elaboration time and its certificate is checked as it streams through a
  FIFO; no certificate bytes reach the disk. Self-contained: the solver is
  the CaDiCaL bundled with the Lean toolchain unless `LRATCATCHER_SOLVER`
  names another. Rebuilds re-run the solver.
-/

namespace LRATCatcher.Tests.StreamCmdTest

lrat_stream php43_streamed "examples/php43/base.cnf"

#print axioms php43_streamed

end LRATCatcher.Tests.StreamCmdTest
