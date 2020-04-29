#!/usr/bin/env bash
source ../common.sh

compile_lean
exec_check "./$f.out"
diff_produced
