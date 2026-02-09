#!/usr/bin/env bash
source ../../common.sh

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
exec_check_raw lean --root=../.. -Dlinter.all=false -DElab.inServer=true "$f"
