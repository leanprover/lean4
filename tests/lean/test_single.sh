#!/usr/bin/env bash
source ../common.sh

# these tests don't have to succeed
exec_capture $LEAN_EXE -DprintMessageEndPos=true -Dlinter.all=false "$f" || true
diff_produced
