#!/usr/bin/env bash
source ../common.sh

compile_lean -shared -o "${f%.lean}.so"
expected_ret=1
exec_check lean -Dlinter.nolint=true --plugin="${f%.lean}.so" "$f"
diff_produced
