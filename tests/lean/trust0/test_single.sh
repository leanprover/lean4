#!/usr/bin/env bash
source ../../common.sh

exec_check lean -t0 -Dlinter.all=false "$f"
