import LRATCatcher.StreamOracle

open LRATCatcher

lrat_stream_cnf leaf1_streamed (LRATCatcher.parseDimacs "p cnf 12 23\n1 0\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n") "examples/php43/leaf1.lrat"

#print axioms leaf1_streamed
