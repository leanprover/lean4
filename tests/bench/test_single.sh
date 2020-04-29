#!/usr/bin/env bash
source ../common.sh

compile_lean
exec_check "./$f.out" $(cat "$f.args")
diff_produced
