#!/usr/bin/env bash
# Capture the manifest Lake hands us at $1 to a known location, then
# return non-zero so the test can inspect the JSON without Lake actually
# building anything downstream. Exit 71 (EX_OSERR) to signal
# "infrastructure failure, not a lean compile error" — Lake will treat
# this as a build failure but the test only cares about the captured
# manifest, not the build outcome.
set -euo pipefail
cp "$1" "$CAPTURED_MANIFEST"
exit 71
