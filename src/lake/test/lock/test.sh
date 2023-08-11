#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../build/bin/lake}

if [ "`uname`" = Darwin ]; then
  TAIL=gtail
else
  TAIL=tail
fi

./clean.sh

# Test lock file creation on build
touch test1.log
$LAKE build Loop 1> test1.log &
test1_pid=$!
grep -q "Building" < <($TAIL --pid=$$ -f test1.log)
test -f build/lake.lock
kill $test1_pid
! wait $test1_pid

# Test build waits when lock file present
touch test2.log
touch build/lake.lock
$LAKE build Test 2> test2.log &
test2_pid=$!
grep -q "waiting" < <($TAIL --pid=$$ -f test2.log)
# Test build resumes on lock file removal
rm build/lake.lock
wait $test2_pid
# Test build success does not leave lock file
test ! -f build/lake.lock

# Test build error still deletes lock file
! $LAKE build Error
test ! -f build/lake.lock
