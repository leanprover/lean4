#!/usr/bin/env bash
source ../common.sh

# Setup directory structure
echo "# SETUP"
./setup.sh

# Valdiate configuration
echo "# TEST: Configuration"
test_no_out -q resolve-deps

# Validate initial directory structure
echo "# TEST: Directory structure"
test_out_diff <(cat << 'EOF'
foo
bar
baz
boo
untraced
untraced
EOF
) -q exe test

# Test Lean<->TOML equivalence
echo "# TEST: Lean->TOML translation"
test_no_out -f lakefileAlt.lean translate-config toml lakefileAlt.produced.toml
test_cmd diff -u --strip-trailing-cr lakefileAlt.expected.toml lakefileAlt.produced.toml
test_no_out -f lakefileAlt.lean -q build --no-build
echo "# TEST: TOML->Lean translation"
test_no_out translate-config lean lakefile.produced.lean
test_cmd diff -u --strip-trailing-cr lakefile.expected.lean lakefile.produced.lean
test_no_out -f lakefile.expected.lean -q build --no-build

# Test input targets
echo "# TEST: input_file target"
test_run query foo
test_cmd diff -u --strip-trailing-cr <(echo foo) "`$LAKE query foo`"
echo "# TEST: input_dir target"
test_run query barz
cat `$LAKE query barz` | diff -u --strip-trailing-cr <(cat << 'EOF'
boo
bar
baz
EOF
) -

# Test input dependencies
echo "# TEST: input_file dependency"
echo traced > inputs/foo.txt
test_eq "traced" exe test foo
echo "# TEST: input_dir dependency"
echo traced > inputs/barz/bar.txt
test_eq "traced" exe test bar
echo traced > inputs/barz/baz.txt
test_eq "traced" exe test baz
echo traced > inputs/barz/bam/boo.txt
test_eq "traced" exe test boo

# Test untraced dependencies
echo "# TEST: Untraced dependencies"
echo traced > inputs/untraced.txt
echo traced > inputs/barz/untraced.txt
test_out_diff <(cat << 'EOF'
traced
traced
traced
traced
untraced
untraced
EOF
) -q exe test

# Cleanup
rm -f produced*
