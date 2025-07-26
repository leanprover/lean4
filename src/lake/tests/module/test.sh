#!/usr/bin/env bash
source ../common.sh

./clean.sh

# ---
# This test covers Lake's interactions with the Lean module system.
# ---

mkdir Test/Generated
cat > Test/Generated/Module.lean <<EOF
module

-- insert here

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
# including promoted imports
test_run build Test.ModulePromoteImport
test_cmd grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/ModulePromoteImport.setup.json
test_run build Test.ModuleTransPromoteImport
test_cmd grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/ModuleTransPromoteImport.setup.json
# should be imported by a non-module
test_run build Test.NonModuleImport
test_cmd grep -F "Test/Generated/Module.olean.private" .lake/build/ir/Test/NonModuleImport.setup.json

# Build all tests before making edits
test_run build

# Tests a public edit of an import
echo "# TEST: public edit"
test_cmd sed_i 's/foo/fu/' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_exp $old_hash != $new_hash
# should trigger a rebuild on a plain `import` in a module
test_out "Built Test.ModuleImport" build Test.ModuleImport -v
test_out "Built Test.ModulePrivateImport" build Test.ModulePrivateImport -v
# should not trigger a rebuild on a transitive private `import` in a module
test_run build Test.ModuleTransPrivateImport --no-build
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module direct import
test_out "Built Test.NonModuleImport" build Test.NonModuleImport -v
# should trigger a rebuild for a non-module transitive import
test_out "Built Test.NonModuleTransImport" build Test.NonModuleTransImport -v

# Tests a private edit of an import
echo "# TEST: private edit"
test_cmd sed_i 's/bar/baz/' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.private.hash)
old_pub_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_pub_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.private.hash)
test_exp $old_pub_hash == $new_pub_hash
test_exp $old_hash != $new_hash
# should not trigger a rebuild on a plain `import` in a module
test_run build Test.ModuleImport --no-build
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
test_out "Built Test.ModulePromoteImport" build Test.ModulePromoteImport -v
# should trigger a rebuild for a non-module direct import
test_out "Built Test.NonModuleImport" build Test.NonModuleImport -v
# should trigger a rebuild for a non-module transitive import
test_out "Built Test.NonModuleTransImport" build Test.NonModuleTransImport -v

# Tests a server edit of an import
echo "# TEST: server edit"
test_cmd sed_i '/-- insert here/{G;}' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.server.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.server.hash)
test_exp $old_hash != $new_hash
# should not trigger a rebuild on a plain `import` in a module
test_run build Test.ModuleImport --no-build
# should trigger a rebuild on an `import all` in a module
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module direct import
test_out "Built Test.NonModuleImport" build Test.NonModuleImport -v
# should trigger a rebuild for a non-module transitive import
test_out "Built Test.NonModuleTransImport" build Test.NonModuleTransImport -v

# Tests a meta edit of an import
echo "# TEST: meta edit"
test_cmd sed_i 's/baz/ipsum/' Test/Generated/Module.lean
old_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.ir.hash)
old_pub_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
test_out "Built Test.Generated.Module" build Test.Generated.Module -v
new_pub_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.olean.hash)
new_hash=$(cat .lake/build/lib/lean/Test/Generated/Module.ir.hash)
test_exp $old_pub_hash == $new_pub_hash
test_exp $old_hash != $new_hash
# should not trigger a rebuild on a plain `import` in a module
test_run build Test.ModuleImport --no-build
# should trigger a rebuild on a `meta import`
test_out "Built Test.ModuleMetaImport" build Test.ModuleMetaImport -v
test_out "Built Test.ModulePrivateMetaImport" build Test.ModulePrivateMetaImport -v
# should trigger a rebuild on a transitive `meta import`
test_out "Built Test.ModuleMetaTransImport" build Test.ModuleMetaTransImport -v
# should trigger a rebuild on module transitive import of a `public meta import`
test_out "Built Test.ModuleTransMetaImport" build Test.ModuleTransMetaImport -v
# should not trigger a rebuild on module transitive import of a private `meta import`
test_run build Test.ModuleTransPrivateMetaImport --no-build
# should trigger a rebuild on an `import all`
test_out "Built Test.ModuleImportAll" build Test.ModuleImportAll -v
# should trigger a rebuild for a non-module direct import
test_out "Built Test.NonModuleImport" build Test.NonModuleImport -v
# should trigger a rebuild for a non-module transitive import
test_out "Built Test.NonModuleTransImport" build Test.NonModuleTransImport -v

# Cleanup
rm -f produced*
