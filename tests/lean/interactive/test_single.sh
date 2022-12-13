#!/usr/bin/env bash
source ../../common.sh

# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

# these tests don't have to succeed
exec_capture lean -Dlinter.all=false --run run.lean "$f" || true

rootDirUri="file://$(git rev-parse --show-toplevel)"
sed -i "s#${rootDirUri}#file://__root__#g" "$f.produced.out"

diff_produced
