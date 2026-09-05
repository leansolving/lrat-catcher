import LRATCatcher.Examples.Schur4CC.Base
import LRATCatcher.Examples.Schur4CC.Cover
import LRATCatcher.Examples.Schur4CC.Chunk1

open Std.Sat LRATCatcher

namespace LRATCatcher.Examples.Schur4CC

def cubesGrp1 : List Cube := chunkCubes1

set_option maxHeartbeats 0 in
theorem cubes_eq : cubes = cubesGrp1 := by native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem grp1_ok : ∀ c ∈ cubesGrp1, (Cube.leafCNF c base).Unsat :=
  chunk1_ok

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem base_unsat : base.Unsat :=
  LRATCatcher.cover_unsat
    (fun c hc => (grp1_ok) c (cubes_eq ▸ hc))
    coverThm

#print axioms base_unsat

end LRATCatcher.Examples.Schur4CC
