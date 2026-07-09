#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test that a precompiled module absent from its parent library's shared target
# is loaded as an individual dylib when elaborating a downstream module that imports it.
PKG="precompileModules_x2ddetached"
test_out "${PKG}_Upstream_Detached.$SHARED_LIB_EXT" -v setup-file ImportDetached.lean
test_out "${PKG}_Upstream_Detached.$SHARED_LIB_EXT" -v setup-file Downstream/ImportDetached.lean

# This segfaults if the individual module dynlib isn't loaded.
test_run build -R Downstream.ImportImportDetached

# cleanup
rm -f produced.out
