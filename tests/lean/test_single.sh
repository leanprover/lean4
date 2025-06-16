#!/usr/bin/env bash
source ../common.sh

# these tests don't have to succeed
exec_capture lean -DprintMessageEndPos=true -Dlinter.all=false -DElab.async=true "$f" || true
diff_produced
