#!/usr/bin/env bash
source ../../common.sh

exec_check ${LEAN_EXE} -t0 -Dlinter.all=false "$f"
