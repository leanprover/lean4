#!/usr/bin/env bash
source ../../common.sh

exec_check_raw lean -Dlinter.all=false -DElab.async=true "$f"
