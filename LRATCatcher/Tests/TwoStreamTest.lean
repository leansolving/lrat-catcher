import LRATCatcher.StreamOracle

/-!
  TwoStreamTest — two streamed imports in one module. The two PHP(4,3)
  leaves (cubes `1` and `-1` of examples/php43/) are imported with
  `lrat_stream_cnf`, each reading its certificate from a regular file
  (examples/php43/leaf{1,2}.lrat, paths relative to the package root, so
  build with `lake build LRATCatcher.Tests.TwoStreamTest` or run
  `lake env lean` from the root; no environment variable, FIFO, or solver).
  The two theorems are composed into one. Each import declares its own
  opaque feed constant (`leaf1_feed`, `leaf2_feed`), so each native axiom is
  pinned only to the blocks its own run observed and the axiom set stays
  jointly satisfiable; the check below fails if the two axioms mention the
  same feed constant or the shared `LRATCatcher.certFeed`.
  Trust base of the composition: 3 standard axioms + one `native_decide`
  axiom per import (`#print axioms` below).
-/

namespace LRATCatcher.Tests.TwoStreamTest

/-- examples/php43/leaf1.cnf: the base formula plus the unit cube `1`. -/
def c1 : String := "p cnf 12 23\n1 0\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n"

/-- examples/php43/leaf2.cnf: the base formula plus the unit cube `-1`. -/
def c2 : String := "p cnf 12 23\n-1 0\n1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n-1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n-2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n-3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n"

lrat_stream_cnf leaf1 (LRATCatcher.parseDimacs c1) "examples/php43/leaf1.lrat"
lrat_stream_cnf leaf2 (LRATCatcher.parseDimacs c2) "examples/php43/leaf2.lrat"

theorem both : (LRATCatcher.parseDimacs c1).Unsat ∧ (LRATCatcher.parseDimacs c2).Unsat :=
  ⟨leaf1, leaf2⟩

#print axioms both

/-! The types of the two native axioms, and the check that their feed
    constants differ and neither is the shared `LRATCatcher.certFeed`. -/

#check @leaf1._native.native_decide.ax_1
#check @leaf2._native.native_decide.ax_1

open Lean Meta in
run_meta do
  let ns := `LRATCatcher.Tests.TwoStreamTest
  let feeds ← [`leaf1, `leaf2].mapM fun n => do
    let ax := ns ++ n ++ `_native.native_decide.ax_1
    let some (.axiomInfo v) := (← getEnv).find? ax
      | throwError "{ax} is not an axiom"
    let consts := v.type.getUsedConstants
    if consts.contains ``LRATCatcher.certFeed then
      throwError "{ax} mentions the shared LRATCatcher.certFeed"
    match consts.filter (fun c => c.toString.endsWith "_feed") with
    | #[f] => pure f
    | fs => throwError "{ax} mentions {fs.size} feed constants: {fs}"
  match feeds with
  | [f1, f2] =>
    if f1 == f2 then throwError "both native axioms mention {f1}"
    logInfo m!"distinct feed constants: {f1}, {f2}"
  | _ => throwError "unexpected"

end LRATCatcher.Tests.TwoStreamTest
