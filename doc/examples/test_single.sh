#!/usr/bin/env bash
source ../../tests/common.sh

exec_check_raw lean -Dlinter.all=false "$f"
