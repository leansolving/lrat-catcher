import LRATCatcher.Examples.Schur4CC.Base

open Std.Sat LRATCatcher

namespace LRATCatcher.Examples.Schur4CC

set_option maxHeartbeats 0 in
theorem coverThm : (negCubesCNF cubes).Unsat :=
  LRATCatcher.checkLratCnf_sound _ "9 2 -1 0 4 3 0
10 2 1 0 7 8 0
11 -2 -1 0 1 2 0
12 -2 1 0 6 5 0
13 -1 0 9 11 0
14 1 0 10 12 0
15 1 0 14 0
16 0 15 13 0
" (by native_decide)

end LRATCatcher.Examples.Schur4CC
