#!/usr/bin/env bash
source ../common.sh

exec_check ${LEAN_EXE} -Dlinter.all=false --run "$f"
diff_produced
