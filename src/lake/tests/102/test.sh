#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

$LAKE build

test -f build/lib/TBA.olean
test -f build/lib/TBA/Eulerian.olean
test -f build/lib/TBA/Eulerian/A.olean
