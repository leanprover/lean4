#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# Tests the `requiresModuleSystem` flag and its companion `allowNonModules`
# opt-out.
#
# `requiresModuleSystem = true` should cause Lake to warn
# whenever a module imports it without a `module` header -- both for downstream
# consumers and for non-module files within the package itself. An importing
# package or library can opt out by setting `allowNonModules = true`.
#
# The lakefiles are generated here rather than committed as the opt-out phase
# mutates them (to add `allowNonModules`).
# ---

# Generate the base lakefiles (without `allowNonModules`).
cat > lakefile.toml <<'EOF'
name = "test"
defaultTargets = ["Test"]

[[lean_lib]]
name = "Test"
globs = "Test.+"

[[require]]
name = "dep"
path = "dep"
EOF

cat > dep/lakefile.toml <<'EOF'
name = "dep"
requiresModuleSystem = true

[[lean_lib]]
name = "Dep"

[[lean_lib]]
name = "DepLegacy"
EOF

# Warm up: create the manifest and resolve dependencies so subsequent
# invocations don't emit setup messages that would confuse the warning checks.
test_run resolve-deps

# A consumer that uses the module system: should build without emitting our warning.
test_not_out "designed for use with the module system" build Test.ModuleConsumer

# A non-module consumer: should build successfully but emit the warning,
# naming both the importing file and the imported package.
test_out "imports \`Dep\` from package \`dep\`, which is designed for use with the module system" \
  build Test.NonModuleConsumer

# Same-package non-module file: dep itself contains DepLegacy.lean (no module
# header) which imports another module of dep. The warning must fire here too,
# since `requiresModuleSystem` applies within the package.
test_out "missing \`module\` header as required by the \`requiresModuleSystem\` option" \
  build "@dep/DepLegacy"

# Opt out via `allowNonModules`, exercising both granularities: set it on the
# `Test` library (per-library opt-out, as one might for a test library) and on
# the `dep` package as a whole.
cat > lakefile.toml <<'EOF'
name = "test"
defaultTargets = ["Test"]

[[lean_lib]]
name = "Test"
allowNonModules = true
globs = "Test.+"

[[require]]
name = "dep"
path = "dep"
EOF

cat > dep/lakefile.toml <<'EOF'
name = "dep"
allowNonModules = true
requiresModuleSystem = true

[[lean_lib]]
name = "Dep"

[[lean_lib]]
name = "DepLegacy"
EOF

# After a clean rebuild, neither warning should appear.
test_run clean
test_not_out "module system" build Test.NonModuleConsumer "@dep/DepLegacy"
no_match_text "missing \`module\` header as required by \`requiresModuleSystem\`" produced.out

rm -f produced*
