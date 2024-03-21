#!/usr/bin/env bash
source ../../common.sh

exec_check lean -Dlinter.all=false "$f"
