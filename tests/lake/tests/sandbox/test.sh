#!/usr/bin/env bash
source ../common.sh

# Tests that the commands which load the workspace re-run themselves under `bwrap`, and which
# grants each of them gets.

./clean.sh

if [ "`uname`" != Linux ]; then
  echo "Skipping test: the Lake sandbox needs Linux namespaces"
  exit 0
fi

# User namespaces cannot be assumed available in CI containers; see `../fake-bwrap.sh`. The shim
# isolates nothing, so this checks the `bwrap` command lines that `log-bwrap.sh` records.
LOG="$PWD/bwrap.log"
export COMPARATOR_BWRAP="$PWD/log-bwrap.sh"
unset LAKE_INADVISABLY_NO_SANDBOX LAKE_SANDBOX

copy_to_work lakefile.toml Lib.lean Main.lean
mkdir .git
PROJ="$(pwd -P)"

# The sandbox has to be asked for.
test_run check-build
test_exp ! -e "$LOG"
test_run --sandbox check-build
test_exp -s "$LOG"
rm -f "$LOG"
export LAKE_SANDBOX=1

# Collects the sandboxed runs of `lake <args>` in `runs.log`.
runs_of() {
  grep -- " $1\$" "$LOG" > runs.log || true
}

# A build first resolves dependencies, the only step with a network and a writable manifest, and
# then runs the command itself without either.
test_run build
test_exp -f .lake/build/lib/lean/Lib.olean
test_exp -s lake-manifest.json
runs_of resolve-deps
match_text "--share-net" runs.log
match_text "--bind $PROJ/lake-manifest.json $PROJ/lake-manifest.json" runs.log
match_text "--ro-bind $PROJ $PROJ" runs.log
match_text "--bind $PROJ/.lake $PROJ/.lake" runs.log
runs_of build
test_exp "$(wc -l < runs.log)" = 1
no_match_text "--share-net" runs.log
no_match_text "lake-manifest.json" runs.log
match_text "--tmpfs /home" runs.log
match_text "--tmpfs /run" runs.log
match_text "--ro-bind $PROJ $PROJ" runs.log
match_text "--bind $PROJ/.lake $PROJ/.lake" runs.log
match_text "--chdir $PROJ" runs.log
no_match_text "--bind $PROJ $PROJ" runs.log

# The child keeps Lean's and Lake's own variables and loses the rest of the environment.
export LEAN_SANDBOX_TEST=kept SANDBOX_TEST_SECRET=secret LAKE_CACHE_KEY=secret
test_out "kept" env printenv LEAN_SANDBOX_TEST
test_out "/tmp/home" env printenv HOME
test_out "1" env printenv LAKE_INADVISABLY_NO_SANDBOX
test_fails env printenv SANDBOX_TEST_SECRET
test_fails env printenv LAKE_CACHE_KEY
unset LEAN_SANDBOX_TEST SANDBOX_TEST_SECRET LAKE_CACHE_KEY

# The command's exit code is the sandbox's.
test_status 3 env sh -c 'exit 3'
test_status 1 build +Missing

# `lake exe` only builds in the sandbox. The program runs outside of it, as the caller.
rm -f "$LOG"
SANDBOX_TEST_SECRET=shown test_out "secret=shown" exe hello
SANDBOX_TEST_SECRET=shown test_status 4 exe hello arg
runs_of "exe hello"
no_match_text "--share-net" runs.log
match_text "--setenv LAKE_EXE_INFO" runs.log

# `lake update` is the resolution, so it runs once, with a network and the manifest.
rm -f "$LOG"
test_run update
test_exp "$(grep -c -- '--chdir' "$LOG")" = 1
runs_of update
match_text "--share-net" runs.log
match_text "--bind $PROJ/lake-manifest.json $PROJ/lake-manifest.json" runs.log
no_match_text "--bind $PROJ $PROJ" runs.log

# So does a command that updates on load.
rm -f "$LOG"
test_run build --update
test_exp "$(grep -c -- '--chdir' "$LOG")" = 1
runs_of "build --update"
match_text "--share-net" runs.log

# Leading options reach the resolution too, and a working directory outside the project is kept.
rm -f "$LOG"
(cd .. && test_run -d work -Kfoo=bar build)
runs_of "-d work -Kfoo=bar resolve-deps"
match_text "--share-net" runs.log
runs_of "-d work -Kfoo=bar build"
match_text "--chdir ${PROJ%/work}" runs.log

# Both opt-outs win over the request and leave `bwrap` alone.
rm -f "$LOG"
test_run --inadvisably-no-sandbox build
LAKE_INADVISABLY_NO_SANDBOX=1 test_run build
test_exp ! -e "$LOG"

# Nothing of the workspace is loaded without a configuration file, so there is nothing to contain.
mkdir empty
test_run -d empty env true
test_exp ! -e "$LOG"

# A `bwrap` that is missing or cannot create namespaces is an error.
COMPARATOR_BWRAP=false test_status_out 1 "cannot create a sandbox here" build
COMPARATOR_BWRAP=lake-missing-sandbox test_status_out 1 "was not found" build
COMPARATOR_BWRAP=false test_run --inadvisably-no-sandbox build
test_exp ! -e "$LOG"

# Sandboxed builds get a Lake cache of their own in place of the regular one.
rm -f "$LOG"
mkdir cache
LAKE_CACHE_DIR="$PROJ/cache" test_run check-build
test_exp -d cache-sandbox
runs_of check-build
match_text "--bind $PROJ/cache-sandbox $PROJ/cache" runs.log
no_match_text "--bind $PROJ/cache $PROJ/cache" runs.log

# A command that edits the sources gets the project writable, except for its `.git`.
test_run translate-config lean
test_exp -f lakefile.lean
runs_of "translate-config lean"
match_pat "--bind $PROJ $PROJ .*--ro-bind $PROJ/.git $PROJ/.git" runs.log

rm -f produced.out "$LOG"
