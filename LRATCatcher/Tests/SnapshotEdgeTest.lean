import LRATCatcher.Stream
import LRATCatcher.Reflect

/-!
  Edge cases of snapshots, compaction and clause ids. These checks document
  the behavior of the definitions in `LRATCatcher.Stream` on inputs that the
  step checks never produce themselves (`serialize` writes a hole at position
  `0` and variables from `1` on). None of them affects soundness: the step
  lemmas conclude unsatisfiability of `restoreD prev`, whatever `prev` is, and
  a successful step check compares the next snapshot with `serialize` (or
  `compactSnapshot ∘ serialize`) of the state it reached.
-/

open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal

namespace LRATCatcher.Tests

/-- The clauses of a state as literal lists (0-based variables), in id order. -/
def stateLits (s : State) : List (List (Nat × Bool)) :=
  s.toCNF.clauses.toList.map (·.literals)

/-! ## A clause at position 0 is dropped by `restoreD`

Position `0` stands for id `0`, which no clause has; `restoreD` drops it
whatever it holds. -/

example (o : Option (List (Nat × Bool))) (rest : Snapshot) :
    restoreD (o :: rest) = restoreD (none :: rest) := rfl

def snapPos0 : Snapshot := [some [(1, true)], some [(2, true)]]

#guard stateLits (restoreD snapPos0) == [[(1, true)]]
#guard serialize (restoreD snapPos0) == [none, some [(2, true)]]

/-! ## A literal with variable 0 collides with variable 1

Snapshot variables are 1-based; `restoreClause` subtracts one, and in `Nat`
`0 - 1 = 0`. -/

example : restoreD [none, some [(0, true)]] = restoreD [none, some [(1, true)]] := by
  simp [restoreD, restoreClause]

#guard serialize (restoreD [none, some [(0, true)]]) == [none, some [(1, true)]]
-- A clause that is not a tautology in the snapshot restores to one.
#guard stateLits (restoreD [none, some [(0, true), (1, false)]]) == [[(0, true), (0, false)]]
-- The text format cannot express variable 0: `0` ends a clause line, so the
-- printed clause `0 0` reads back as the empty clause.
#guard printSnap [none, some [(0, true)]] == ".\n0 0\n"
#guard parseSnap (printSnap [none, some [(0, true)]]) == [none, some []]

/-! ## Compaction of a snapshot that is not a `serialize` image

`toCNF_restoreD_compactSnapshot_serialize` covers `serialize` images. Any
snapshot with a hole at position 0 compacts to the same CNF as well (the
example below). A clause at position 0 is different: `restoreD` drops it, but
`compactSnapshot` keeps it as the first live clause, so the two CNFs differ. -/

example (rest : Snapshot) :
    (restoreD (compactSnapshot (none :: rest))).toCNF = (restoreD (none :: rest)).toCNF := by
  simp only [restoreD, compactSnapshot, State.toCNF, List.tail_cons]
  congr 1
  apply Array.toList_inj.mp
  simp only [id_eq, List.filterMap_cons_none, List.map_filterMap, List.map_toArray,
    Option.map_map, Function.comp_def, Option.map_some, List.size_toArray,
    List.filterMap_toArray', List.filterMap_filterMap, List.length_map, List.filterMap_map]
  congr 1
  funext o
  cases o <;> rfl

def snapHoles : Snapshot := [none, some [(1, true)], none, none, some [(2, false)], none]

#guard compactSnapshot snapHoles == [none, some [(1, true)], some [(2, false)]]
#guard stateLits (restoreD (compactSnapshot snapHoles)) == stateLits (restoreD snapHoles)

def snapPos0Holes : Snapshot := [some [(3, true)], none, some [(1, true)]]

#guard compactSnapshot snapPos0Holes == [none, some [(3, true)], some [(1, true)]]
#guard stateLits (restoreD snapPos0Holes) == [[(0, true)]]
#guard stateLits (restoreD (compactSnapshot snapPos0Holes)) == [[(2, true)], [(0, true)]]

/-! ## Printed clause ids are ignored; hints name positions

The checker gives the `i`-th clause (input clauses first, then additions in
order) the id `i`, whatever id the certificate prints. Hints are read as these
ids. `tiny.lrat` prints ids 5, 6, 7, which match; below, the same deduction
with printed ids 15, 16, 17. -/

/-- Kernel-mode view of an LRAT text (actions as parsed, `[]` on error). -/
def edgeActions (s : String) : List IntAction :=
  match parseLRATProof s.toUTF8 with
  | .ok p => p.toList
  | .error _ => []

-- Printed ids 15, 16, 17, hints by position (5, 6): accepted by the native
-- checker, the kernel checker and the stream path.
def idsShifted : String := "15 1 0 1 3 0\n16 2 0 5 2 0\n17 0 5 6 4 0\n"

#guard checkLrat (include_str "tiny.cnf") idsShifted
#guard checkKernel (parseDimacs (include_str "tiny.cnf")) (edgeActions idsShifted)
#guard stepFinish (serialize (.ofCNF (parseDimacs (include_str "tiny.cnf"))))
  (parseActions idsShifted)

-- Printed ids 15, 16, 17, hints by printed id (15, 16): no clause has id 15
-- or 16, so all three reject.
def idsAsPrinted : String := "15 1 0 1 3 0\n16 2 0 15 2 0\n17 0 15 16 4 0\n"

#guard checkLrat (include_str "tiny.cnf") idsAsPrinted = false
#guard checkKernel (parseDimacs (include_str "tiny.cnf")) (edgeActions idsAsPrinted) = false
#guard stepFinish (serialize (.ofCNF (parseDimacs (include_str "tiny.cnf"))))
  (parseActions idsAsPrinted) = false

end LRATCatcher.Tests
