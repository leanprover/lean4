#!/usr/bin/env bash
set -euxo pipefail

echo "lock file currently disabled; skipping test"
exit 0

LAKE=${LAKE:-../../.lake/build/bin/lake}

unamestr=`uname`
if [ "$unamestr" = Darwin ] || [ "$unamestr" = FreeBSD ]; then
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
test -f .lake/build/lake.lock
kill $test1_pid
wait $test1_pid  && exit 1 || true

# Test build waits when lock file present
touch test2.log
touch .lake/build/lake.lock
$LAKE build Nop 2> test2.log &
test2_pid=$!
grep -q "waiting" < <($TAIL --pid=$$ -f test2.log)
# Test build resumes on lock file removal
rm .lake/build/lake.lock
wait $test2_pid
# Test build success does not leave lock file
test ! -f .lake/build/lake.lock

# Test build error still deletes lock file
$LAKE build Error && exit 1 || true
test ! -f .lake/build/lake.lock

# Test that removing the lock during build does not cause it to fail
touch test3.log
$LAKE build Wait > test3.log 2>&1 &
test3_pid=$!
grep -q "Building" < <($TAIL --pid=$$ -f test3.log)
rm .lake/build/lake.lock
wait $test3_pid
cat test3.log | grep --color "deleted before the lock"
