#!/usr/bin/env bash
source ../common.sh

# these tests don't have to succeed
# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
exec_capture lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true "$f" || true
diff_produced
