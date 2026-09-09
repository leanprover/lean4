#!/usr/bin/env bash
source ../common.sh

./clean.sh

echo "# TEST: without --fail-fast, an early failure does not stop other targets"
test_err "Some required targets logged failures" build
test_exp -f slowA.produced.out
test_exp -f slowB.produced.out
test_exp -f slowC.produced.out
test_exp -f .lake/build/lib/lean/Slow.olean

./clean.sh

echo "# TEST: --fail-fast stops scheduling new jobs after the first failure"
test_err "Some required targets logged failures" build --fail-fast
test_exp -f slowA.produced.out
test_exp ! -f slowB.produced.out
test_exp ! -f slowC.produced.out
test_exp ! -f .lake/build/lib/lean/Slow.olean

# Canceled jobs must not appear in the failure summary (their log is trace-level).
if grep -E '^- (slowB|slowC|Slow)$' produced.out; then
  echo "FAILURE: canceled job listed as a failure"
  exit 1
fi
