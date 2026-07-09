import LRATCatcher.StreamOracle

/-!
  StreamCmdTest — the `lrat_stream` command end-to-end: cadical is launched
  at elaboration time and its certificate is checked as it streams through a
  FIFO; no certificate bytes reach the disk. Self-contained apart from
  `cadical` on PATH (beware: under `lake`, plain `cadical` resolves to the
  version bundled with the Lean toolchain). Rebuilds re-run the solver.
-/

namespace LRATCatcher.Tests.StreamCmdTest

lrat_stream php43_streamed "examples/php43/base.cnf"

#print axioms php43_streamed

end LRATCatcher.Tests.StreamCmdTest
