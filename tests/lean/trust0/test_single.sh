#!/usr/bin/env bash
source ../../common.sh

exec_check_raw lean -t0 -Dlinter.all=false "$f"
