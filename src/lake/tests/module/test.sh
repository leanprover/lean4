#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# This test covers Lake's interactions with the Lean module system.
# ---

mkdir Test/Generated
cat > Test/Generated/Module.lean <<EOF
module

-- delete me

/-- docstring A -/
public def foo := "bar"
EOF

# Tests importing of a module's private segment
# should not not be imported by a plain `import` in a module
test_run build Test.ModuleImport
test_cmd_fails grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/ModuleImport.setup.json
# should be imported by an `import all` in a module
test_run build Test.ModuleImportAll
test_cmd grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/ModuleImportAll.setup.json
# should be imported by a non-module
test_run build Test.NonModule
test_cmd grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/NonModule.setup.json

# Tests a public edit of an import
echo "# TEST: public edit"
test_cmd sed_i 's/foo/fu/' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_exp $old_hash != $new_hash
# should trigger a rebuild on a plain `import` in a module
test_out "Built Test.ModuleImport" build Test.ModuleImport -v
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module
test_out "Built Test.NonModule" build Test.NonModule -v

# Tests a private edit of an import
echo "# TEST: private edit"
test_cmd sed_i 's/bar/baz/' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.private.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.private.hash)
test_exp $old_hash != $new_hash
# should not trigger a rebuild on a plain `import` in a module
test_run build Test.ModuleImport --no-build
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module
test_out "Built Test.NonModule" build Test.NonModule -v

# Tests a server edit of an import
echo "# TEST: server edit"
test_cmd sed_i '/-- delete me/{N;d;}' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.server.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.server.hash)
test_exp $old_hash != $new_hash
# should not trigger a rebuild on a plain `import` in a module
test_run build Test.ModuleImport --no-build
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module
test_out "Built Test.NonModule" build Test.NonModule -v

# Cleanup
rm -f produced*
