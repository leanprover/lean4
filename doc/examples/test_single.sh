#!/usr/bin/env bash
source ../../tests/common.sh

exec_check lean -Dlinter.all=false "$f"
