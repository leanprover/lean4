#!/usr/bin/env bash
source ../../common.sh

# Elab.inServer to allow for arbitrary `#eval`
exec_check_raw lean -Dlinter.all=false -Dexperimental.module=true -DElab.inServer=true "$f"
