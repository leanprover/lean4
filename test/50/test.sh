#!/usr/bin/env bash
set -exo pipefail

LAKE=${LAKE:-../../../build/bin/lake}

cd foo
rm -rf build
${LAKE} build -v -KleanArgs=-Dhygiene=true -K leancArgs=-DBAR | grep -m2 foo.c
${LAKE} build -v -KleanArgs=-Dhygiene=false -K leancArgs=-DBAZ | grep -m2 foo.c
${LAKE} build -v -KleanArgs=-Dhygiene=false -K leancArgs=-DBAR | grep -m1 foo.o
${LAKE} build -v -KleanArgs=-Dhygiene=true -K leancArgs=-DBAR | grep -m1 foo.olean
