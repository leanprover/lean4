#!/usr/bin/env bash
source ../common.sh

exec_check lean --run "$f"
diff_produced
