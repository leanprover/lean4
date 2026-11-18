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

# Canceled jobs must not appear in the failure summary.
if grep -E '^- (slowB|slowC|Slow)$' produced.out; then
  echo "FAILURE: canceled job listed as a failure"
  exit 1
fi

# Canceled jobs are reported as canceled: neither a failure nor a success.
test_exp -n "$(grep -E '^⊘ .*Canceled (slowB|slowC|Slow)$' produced.out)"
if grep -E '(✔|✖) .*(slowB|slowC|Slow)$' produced.out; then
  echo "FAILURE: canceled job reported as built or failed"
  exit 1
fi

# The cancellation must not be misreported as a bad import.
if grep -E 'bad import' produced.out; then
  echo "FAILURE: cancellation misreported as a bad import"
  exit 1
fi
