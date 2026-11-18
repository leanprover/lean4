#!/usr/bin/env bash
source ../common.sh
./clean.sh

# Downstream executables link Lake statically (see `LEANC_STATIC_LINKER_FLAGS`), so every
# toolchain library Lake pulls in must be on that link line. Importing `Lake.All` initializes
# every Lake module and thus exercises all of those references.

test_run build
test_cmd_out "Lake " ./.lake/build/bin/main

# Cleanup
rm -f produced.out
