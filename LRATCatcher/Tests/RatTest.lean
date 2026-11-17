import LRATCatcher.Reflect

/-!
  RAT steps with hint groups, in native and kernel mode.

  `rat.lrat` refutes the tiny instance (`tiny.cnf`) through two RAT additions:
  * step 5 adds `3`, a fresh variable: no live clause contains `-3`, so the
    RAT check needs no hint group;
  * step 6 adds `-3 1` with pivot `-3` and one hint group `-5 1 3`: clause 5
    is the only live clause with the negated pivot `3`, its resolvent with the
    new clause is `1`, and RUP on hints 1 and 3 (`1 2`, `1 -2`) derives it;
  * steps 7 to 9 are RUP and end in the empty clause.

  `rat_bad.lrat` drops the hint group of step 6. The groups then no longer
  cover every live clause with the negated pivot, so both checkers reject the
  certificate (negative control).
-/

namespace LRATCatcher.Tests

lrat_reflect rat_native "LRATCatcher/Tests/tiny.cnf" "LRATCatcher/Tests/rat.lrat"

#print axioms rat_native

lrat_reflect +kernel rat_kernel "LRATCatcher/Tests/tiny.cnf" "LRATCatcher/Tests/rat.lrat"

#print axioms rat_kernel

/-- Actions of an LRAT text, `[]` on a parse error (as the kernel commands see
    them). -/
def ratTestActions (s : String) : List Std.Tactic.BVDecide.LRAT.IntAction :=
  match Std.Tactic.BVDecide.LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p.toList
  | .error _ => []

-- Both checkers accept the certificate with the hint group ...
#guard checkLrat (include_str "tiny.cnf") (include_str "rat.lrat")
#guard checkKernel (parseDimacs (include_str "tiny.cnf")) (ratTestActions (include_str "rat.lrat"))

-- ... and reject it without (the RAT hint groups are not exhaustive).
#guard checkLrat (include_str "tiny.cnf") (include_str "rat_bad.lrat") = false
#guard checkKernel (parseDimacs (include_str "tiny.cnf"))
  (ratTestActions (include_str "rat_bad.lrat")) = false

-- The two certificates differ only in the hint group of step 6.
#guard (ratTestActions (include_str "rat.lrat")).eraseIdx 1 ==
  (ratTestActions (include_str "rat_bad.lrat")).eraseIdx 1
#guard (ratTestActions (include_str "rat.lrat"))[1]! ==
  .addRat 6 #[-3, 1] (3, false) #[] #[(5, #[1, 3])]
#guard (ratTestActions (include_str "rat_bad.lrat"))[1]! ==
  .addRat 6 #[-3, 1] (3, false) #[] #[]

end LRATCatcher.Tests
