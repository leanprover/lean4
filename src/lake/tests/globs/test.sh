#!/usr/bin/env bash
set -euxo pipefail

# tests issue 174
# also tests the issue reported on this Zulip thread:
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20build.20all/near/370788618

./clean.sh
LAKE=${LAKE:-../../build/bin/lake}
$LAKE build -v
