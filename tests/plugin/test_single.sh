#!/usr/bin/env bash
source ../common.sh

compile_lean -shared -o "${f%.lean}.so"
expected_ret=1
exec_check lean -Dlinter.all=false --plugin="${f%.lean}.so" "$f"
diff_produced
