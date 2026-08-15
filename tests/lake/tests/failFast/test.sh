#!/usr/bin/env bash
source ../common.sh

# The pool must fit the two token-waiting jobs plus Fail's compile; the
# targets synchronize on cancellation itself (see lakefile.lean), so the
# assertions do not race the wall clock.
export LEAN_NUM_THREADS=8
export FAILFAST_SYNC="$PWD/slowA.produced.out"

./clean.sh

echo "# TEST: --fail-fast fails the build and stops scheduling new jobs"
test_err "Some required targets logged failures" build --fail-fast
test_exp -f slowA.produced.out
test_exp ! -f slowB.produced.out
test_exp ! -f .lake/build/lib/lean/SlowChain/B.olean
