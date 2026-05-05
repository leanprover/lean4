#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Tests the package-level `requiresModuleSystem` flag.
# A package that sets `requiresModuleSystem = true` should cause Lake
# to warn whenever a downstream module imports it without a `module` header.
# ---

# Warm up: create the manifest and resolve dependencies so subsequent
# invocations don't emit setup messages that would confuse the warning checks.
test_run resolve-deps

# A consumer that uses the module system: should build without emitting our warning.
test_not_out "designed for use with the module system" build Test.ModuleConsumer

# A non-module consumer: should build successfully but emit the warning,
# naming both the importing file and the imported package.
test_out "Test/NonModuleConsumer.lean: imports \`Dep\` from package \`dep\`, which is designed for use with the module system" \
  build Test.NonModuleConsumer

# Cleanup
rm -f produced*
