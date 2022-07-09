set -ex
LAKE=${LAKE:-../../build/bin/lake}
$LAKE script list
$LAKE run scripts/greet
$LAKE script run greet me
$LAKE script doc greet
$LAKE script run nonexistant && false || true
$LAKE script doc nonexistant && false || true
$LAKE scripts
