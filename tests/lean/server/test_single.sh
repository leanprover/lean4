#!/usr/bin/env bash
source ../../common.sh

exec_check ${LEAN_EXE} -j 0 -Dlinter.all=false --run "$f"
