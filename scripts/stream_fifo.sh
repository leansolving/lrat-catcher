#!/bin/bash
# Zero-storage streaming import test: PHP(4,3) streamed live from cadical
# through a FIFO into the Lean checker (Tests/StreamOracleTest.lean), run
# N times consecutively (default 5) to stress the cached-handle/initializer
# path (MEM_011: one unexplained sorryAx transient on 2026-07-05).
#
# Each run compiles the test module afresh with `lake env lean`: Lake's
# rebuild check is content-hash based, so `touch` + `lake build` would NOT
# re-run an unchanged check (a run whose solver then blocks on the FIFO
# forever). Certificates are never Lake dependencies.
#
# Usage: scripts/stream_fifo.sh [runs]        (from anywhere; cds to repo root)
set -u
cd "$(dirname "$0")/.."
RUNS="${1:-5}"
TMPD=$(mktemp -d)
FIFO="$TMPD/cert.fifo"
mkfifo "$FIFO" || exit 1
trap 'rm -rf "$TMPD"' EXIT

# build the test module's imports once
lake build LRATCatcher.StreamOracle || exit 1

for i in $(seq 1 "$RUNS"); do
  cadical --lrat --no-binary --no-factor examples/php43/base.cnf "$FIFO" > /dev/null &
  SOLVER=$!
  if ! LRATCATCHER_STREAM_PATH="$FIFO" lake env lean LRATCatcher/Tests/StreamOracleTest.lean; then
    echo "stream_fifo.sh: run $i: check FAILED" 1>&2
    kill "$SOLVER" 2>/dev/null
    exit 1
  fi
  wait "$SOLVER"
  RC=$?
  if [ "$RC" -ne 20 ]; then
    echo "stream_fifo.sh: run $i: solver exit $RC (expected 20)" 1>&2
    exit 1
  fi
  echo "stream_fifo.sh: run $i OK (zero certificate bytes on disk)"
done
echo "stream_fifo.sh: all $RUNS runs OK"
