#!/usr/bin/env bash
set -mexo pipefail

LAKE=${LAKE:-../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  TAIL=gtail
else
  TAIL=tail
fi

./clean.sh

# Test lock file creation on build
$LAKE build Loop 2>&1 > test.log &
grep -q "Building" < <($TAIL --pid=$$ -f test.log)
kill %%
test -f build/lake.lock

# Test build waits when lock file present
$LAKE build Test 2>&1 | tee test.log &
grep -q "waiting" < <($TAIL --pid=$$ -f test.log)
# Test build resumes on lock file removal
rm build/lake.lock
fg
echo "done"
