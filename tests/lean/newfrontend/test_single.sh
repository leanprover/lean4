#!/usr/bin/env bash
source ../../common.sh

exec_check lean -j0 --new-frontend "$f"
