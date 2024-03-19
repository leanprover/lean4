#!/usr/bin/env bash
source ../common.sh

# LEAN_EXPORTING needs to be defined for .c files included in shared libraries
compile_lean_c_backend -shared -o "${f%.lean}.so" -DLEAN_EXPORTING
expected_ret=1
exec_check lean -Dlinter.all=false --plugin="${f%.lean}.so" "$f"
diff_produced
