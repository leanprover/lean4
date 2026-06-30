#!/usr/bin/env bash
source ../common.sh
source ./clean.sh

# Run in a working directory so we can create a Git repository outside the
# checked-in source tree (committing a repo inside a repo is not well-supported).
WORK_DIR="$PWD/work"
mkdir -p "$WORK_DIR"
cp lakefile.lean "$WORK_DIR/"
cd "$WORK_DIR"

# A three-commit history: c1 <- c2 <- c3 (HEAD). Only the SHA passed to the
# `discoverWalk` script is treated as "cached" by its stub lookup.
echo "# SETUP"
set -x
git init
git checkout -b master
git config user.name test
git config user.email test@example.com
git add --all
git commit -m "c1"
git commit --allow-empty -m "c2"
git commit --allow-empty -m "c3"
set +x

ANCESTOR=$(git rev-parse HEAD~2)   # c1
HEAD_REV=$(git rev-parse HEAD)     # c3

echo "# TEST: nearest walks back to a cached ancestor; head consults only HEAD"
test_out "nearest=HIT head=MISS" run discoverWalk "$ANCESTOR"

echo "# TEST: --max-revs=1 bounds the nearest walk to HEAD (miss); head ignores it"
test_out "nearest=MISS head=MISS" run discoverWalk "$ANCESTOR" 1

echo "# TEST: a bound that reaches the ancestor finds it again"
test_out "nearest=HIT head=MISS" run discoverWalk "$ANCESTOR" 3

echo "# TEST: when HEAD itself is cached, both policies find it"
test_out "nearest=HIT head=HIT" run discoverWalk "$HEAD_REV"
