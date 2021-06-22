#!/usr/bin/env bash
source ../../common.sh

# Disable lsan since we are calling exit() in the file worker.
export ASAN_OPTIONS=detect_leaks=0

# these tests don't have to succeed
exec_capture lean --run run.lean "$f" || true
diff_produced
