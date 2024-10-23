#!/usr/bin/env bash
source ../common.sh

exec_check lean -Dlinter.all=false --run "$f" $(cat 2>/dev/null "$f.args")
diff_produced .interpreted
