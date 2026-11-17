import LRATCatcher.Reflect
import LRATCatcher.StreamOracle

/-!
  FactorTest — a certificate with extension variables (bounded variable
  addition, CaDiCaL's "factoring").

  `examples/php76factor/base.cnf` is PHP(7,6) (`examples/gen_php.py 7 6`, 42
  variables, 133 clauses). `factor.lrat` was produced by CaDiCaL 3.0.1 with
  factoring switched on (`cadical --lrat --no-binary --factor=true base.cnf
  factor.lrat`; 3.0.1 does not factor by default): 246 of its 780 additions
  contain one of the 9 extension variables 43-51. The LRAT checker of earlier
  Lean versions bounded the variables and rejected such certificates; the
  checker of this toolchain has no variable bound. The certificate is imported
  in native mode (`lrat_reflect`) and in stream mode from the file
  (`lrat_stream_cnf`).
-/

open Std.Tactic.BVDecide.LRAT LRATCatcher

namespace LRATCatcher.Tests.FactorTest

/-- The largest variable in the clauses a certificate adds. -/
def maxAddedVar (acts : Array IntAction) : Nat :=
  acts.foldl (init := 0) fun m a =>
    match a with
    | .addRup _ c _ | .addRat _ c _ _ _ => c.foldl (init := m) fun m l => max m l.natAbs
    | _ => m

-- The certificate uses extension variables: its largest variable is 51,
-- above the 42 variables of the CNF.
#guard maxAddedVar (parseActions (include_str "../../examples/php76factor/factor.lrat")) == 51
#guard (parseDimacs (include_str "../../examples/php76factor/base.cnf")).clauses.size == 133

lrat_reflect php76_factor "examples/php76factor/base.cnf" "examples/php76factor/factor.lrat"

lrat_stream_cnf php76_factor_streamed
  (LRATCatcher.parseDimacs (include_str "../../examples/php76factor/base.cnf"))
  "examples/php76factor/factor.lrat"

#print axioms php76_factor
#print axioms php76_factor_streamed

end LRATCatcher.Tests.FactorTest
