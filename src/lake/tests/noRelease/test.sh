#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# ---
# Test Lake's behavior when failing to fetch a cloud release
# ---

# Test that a direct invocation fo `lake build *:release` fails
($LAKE build dep:release && exit 1 || true) | diff -u --strip-trailing-cr <(cat << 'EOF'
[1/1] Fetching dep cloud release
info: dep: wanted prebuilt release, but could not find an associated tag for the package's revision
error: failed to fetch cloud release
Some build steps logged failures:
- Fetching dep cloud release
EOF
) -

# Test that an indirect fetch on the release does not cause the build to fail
$LAKE build -v test:extraDep | diff -u --strip-trailing-cr <(cat << 'EOF'
[1/1] Building test:extraDep
info: dep: wanted prebuilt release, but could not find an associated tag for the package's revision
warning: failed to fetch cloud release; falling back to local build
All builds jobs completed successfully.
EOF
) -
