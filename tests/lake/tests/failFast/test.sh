#!/usr/bin/env bash
source ../common.sh

export FAILFAST_SYNC="$PWD/slowA.produced.out"

./clean.sh

echo "# TEST: without --fail-fast, an early failure does not stop other targets"
test_err "Some required targets logged failures" build
test_exp -f slowA.produced.out
test_exp -f slowB.produced.out
test_exp -f .lake/build/lib/lean/SlowChain/B.olean

./clean.sh

echo "# TEST: --fail-fast stops scheduling new jobs after the first failure"
test_err "Some required targets logged failures" build --fail-fast
test_exp -f slowA.produced.out
test_exp ! -f slowB.produced.out
test_exp ! -f .lake/build/lib/lean/SlowChain/B.olean
