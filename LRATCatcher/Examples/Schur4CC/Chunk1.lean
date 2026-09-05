import LRATCatcher.Examples.Schur4CC.Base
import LRATCatcher.StreamOracle

open Std.Sat LRATCatcher

namespace LRATCatcher.Examples.Schur4CC

def cube1 : Cube := [(0, true), (1, true), (2, true)]
def cube2 : Cube := [(0, true), (1, true), (2, false)]
def cube3 : Cube := [(0, true), (1, false), (2, true)]
def cube4 : Cube := [(0, true), (1, false), (2, false)]
def cube5 : Cube := [(0, false), (1, true), (2, true)]
def cube6 : Cube := [(0, false), (1, true), (2, false)]
def cube7 : Cube := [(0, false), (1, false), (2, true)]
def cube8 : Cube := [(0, false), (1, false), (2, false)]
def chunkCubes1 : List Cube := [cube1, cube2, cube3, cube4, cube5, cube6, cube7, cube8]

lrat_stream_cnf leaf1_unsat (Cube.leafCNF cube1 base) "examples/schur4cc/leaves/leaf1"
lrat_stream_cnf leaf2_unsat (Cube.leafCNF cube2 base) "examples/schur4cc/leaves/leaf2"
lrat_stream_cnf leaf3_unsat (Cube.leafCNF cube3 base) "examples/schur4cc/leaves/leaf3"
lrat_stream_cnf leaf4_unsat (Cube.leafCNF cube4 base) "examples/schur4cc/leaves/leaf4"
lrat_stream_cnf leaf5_unsat (Cube.leafCNF cube5 base) "examples/schur4cc/leaves/leaf5"
lrat_stream_cnf leaf6_unsat (Cube.leafCNF cube6 base) "examples/schur4cc/leaves/leaf6"
lrat_stream_cnf leaf7_unsat (Cube.leafCNF cube7 base) "examples/schur4cc/leaves/leaf7"
lrat_stream_cnf leaf8_unsat (Cube.leafCNF cube8 base) "examples/schur4cc/leaves/leaf8"

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem chunk1_ok : ∀ c ∈ chunkCubes1, (Cube.leafCNF c base).Unsat :=
  List.forall_mem_cons.mpr ⟨leaf1_unsat, List.forall_mem_cons.mpr ⟨leaf2_unsat, List.forall_mem_cons.mpr ⟨leaf3_unsat, List.forall_mem_cons.mpr ⟨leaf4_unsat, List.forall_mem_cons.mpr ⟨leaf5_unsat, List.forall_mem_cons.mpr ⟨leaf6_unsat, List.forall_mem_cons.mpr ⟨leaf7_unsat, List.forall_mem_cons.mpr ⟨leaf8_unsat, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end LRATCatcher.Examples.Schur4CC
