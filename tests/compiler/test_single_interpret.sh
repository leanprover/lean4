#!/usr/bin/env bash
source ../common.sh

exec_check lean -Dlinter.all=false --run "$f"
diff_produced
