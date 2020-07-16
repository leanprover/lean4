#!/usr/bin/env bash
source ../../common.sh

# these tests don't have to succeed
lean "$f" > "$f.produced.out" 2>&1 || true
diff_produced
