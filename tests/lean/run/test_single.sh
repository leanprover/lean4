#!/usr/bin/env bash
source ../../common.sh

exec_check lean -j 0 -Dlinter.all=false "$f"
