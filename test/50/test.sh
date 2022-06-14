#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

cd foo
rm -rf build
${LAKE} build -- -Dhygiene=true -DBAR | grep -m2 foo.c
${LAKE} build -- -Dhygiene=false -DBAZ | grep -m2 foo.c
${LAKE} build -- -Dhygiene=false -DBAR | grep -m1 foo.o
${LAKE} build -- -Dhygiene=true -DBAR | grep -m1 foo.olean
