#!/usr/bin/env bash
source ../../tests/common.sh

exec_check lean -j 0 "$f"
