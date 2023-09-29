#!/usr/bin/env bash
source ../../tests/common.sh

exec_check ${LEAN_EXE} -j 0 -Dlinter.all=false "$f"
