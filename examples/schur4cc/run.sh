#!/bin/bash
# End-to-end cube-and-conquer example: S(4) = 44 inside Lean.
#
# Encoding in Lean -> DIMACS -> 8 cubes -> 8 leaf refutations (CaDiCaL) ->
# streamed import (one native_decide axiom per leaf) -> embedded cover
# certificate -> one theorem about the encoder term -> S(4) = 44.
#
# Run from the package root:   bash examples/schur4cc/run.sh
# Needs: Lean (elan), cadical >= 3.0 in PATH (or CADICAL=/path/to/cadical),
# python3. Single core, a few minutes; ~280 MB of certificates land in
# examples/schur4cc/leaves/ (not tracked by git).
set -euo pipefail
cd "$(dirname "$0")/../.."          # package root
EX=examples/schur4cc
LEAVES=$EX/leaves
CADICAL=${CADICAL:-cadical}
TERM_="LRATCatcher.Schur.encodeK 4 45"
SPLIT=${SPLIT:-3}                   # cubes = all 2^SPLIT sign patterns on variables 1..SPLIT

echo "== 1. tools"
lake build lratcatch-gen lratcatch-export lratcatch-cover-stream
BIN=.lake/build/bin

echo "== 2. DIMACS from the Lean encoder ($TERM_)"
$BIN/lratcatch-gen schur 4 45 $EX/schur_4_45.cnf

echo "== 3. cubes: all 2^$SPLIT sign patterns on variables 1..$SPLIT (with SPLIT=3: the colours of the number 1)"
python3 examples/gen_static_cubes.py "$SPLIT" > $EX/cubes.icnf
N=$(grep -c '^a ' $EX/cubes.icnf)

echo "== 4. leaf CNFs (cube units first, then the base) and the negated-cubes CNF"
rm -rf $LEAVES
$BIN/lratcatch-export $EX/schur_4_45.cnf $EX/cubes.icnf $LEAVES

echo "== 5. solve the $N leaves (binary LRAT; a stream is a plain file named leaf<i>)"
solve() {  # solve <cnf> <cert> [flags]: exit code 20 (UNSAT) is the expected outcome
  local cnf=$1 cert=$2; shift 2
  local rc=0
  "$CADICAL" --lrat --no-factor -q "$@" "$cnf" "$cert" || rc=$?
  [ "$rc" -eq 20 ] || { echo "cadical on $cnf: exit $rc, expected 20 (UNSAT)"; exit 1; }
  echo "   $cert: $(wc -c < "$cert") bytes"
}
for i in $(seq 1 "$N"); do
  solve $LEAVES/leaf$i.cnf $LEAVES/leaf$i
done

echo "== 6. cover certificate: the negated cubes are unsatisfiable (ASCII LRAT, embedded)"
solve $LEAVES/negcubes.cnf $EX/cover.lrat --no-binary

echo "== 7. generate the Lean modules (LRATCatcher/Examples/Schur4CC/)"
$BIN/lratcatch-cover-stream $EX/schur_4_45.cnf $EX/cubes.icnf $EX/cover.lrat \
  /dev/null /dev/null /dev/null $LEAVES Schur4CC \
  --base-term "$TERM_" --import LRATCatcher.Showcases.Schur --root LRATCatcher.Examples
rm -f LRATCatcher/Examples/Schur4CC/{build.sh,driver.sh,worker-live.sh,streams.tsv}

echo "== 8. check the certificates as they stream, compose, and state S(4) = 44"
# certificates are not Lake dependencies: drop the example's build products so
# the streams are re-checked on every run (a cached olean would be replayed)
rm -rf .lake/build/lib/lean/LRATCatcher/Examples/Schur4CC .lake/build/ir/LRATCatcher/Examples/Schur4CC
lake build LRATCatcher.Examples.Schur4CC.Final
