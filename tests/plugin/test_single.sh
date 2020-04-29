#!/usr/bin/env bash
source ../common.sh

compile_lean -shared -o "${f%.lean}.so"
expected_ret=1
exec_check lean --plugin="${f%.lean}.so" "$f"
diff_produced
