#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Run DSK tests
test_run -f keys.lean resolve-deps
