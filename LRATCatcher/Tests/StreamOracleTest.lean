import LRATCatcher.StreamOracle

/-!
  StreamOracleTest — zero-storage streaming check of PHP(4,3) via the opaque
  feed. Requires `LRATCATCHER_STREAM_PATH` to name a live LRAT stream for
  `examples/php43/base.cnf` (a FIFO written by a running solver, or a
  certificate file); run it via `scripts/stream_fifo.sh`, which also
  stress-tests repeated runs. A plain `lake build` of this module without
  the environment variable fails (the feed reports end of stream).
  Trust base: 3 standard axioms + ONE `native_decide` axiom for the whole
  streamed check (`#print axioms` below).
-/

namespace LRATCatcher.Tests.StreamOracleTest

def base : String := "p cnf 12 22\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n"

theorem php43_stream : (LRATCatcher.parseDimacs base).Unsat :=
  LRATCatcher.checkStreamCnf_sound (LRATCatcher.parseDimacs base)
    LRATCatcher.certFeed LRATCatcher.streamFuel (by native_decide)

#print axioms php43_stream

end LRATCatcher.Tests.StreamOracleTest
