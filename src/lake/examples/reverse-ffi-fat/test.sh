set -ex

LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

LAKE=$LAKE make run
LAKE=$LAKE make run-local
