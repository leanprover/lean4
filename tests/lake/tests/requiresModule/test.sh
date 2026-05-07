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

# Same-package non-module file: dep itself contains DepLegacy.lean (no module
# header) which imports another module of dep. The warning must fire here too,
# since `requiresModuleSystem` applies within the package.
test_out "DepLegacy.lean: missing \`module\` header as required by \`requiresModuleSystem\` package option" \
  build "@dep/DepLegacy"

# Opt out of the warning by setting `allowNonModules` on the importing package.
# After a clean rebuild, neither the cross-package nor the intra-package warning
# should appear.
sed_i '1a allowNonModules = true' lakefile.toml
sed_i '1a allowNonModules = true' dep/lakefile.toml
test_run clean
test_not_out "module system" build Test.NonModuleConsumer "@dep/DepLegacy"

# Restore the lakefiles and clean up.
sed_i '/^allowNonModules = true$/d' lakefile.toml
sed_i '/^allowNonModules = true$/d' dep/lakefile.toml
rm -f produced*
