#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test `new` and `init` with bad template/language (should error)

echo "# TEST: Template validation"
test_err "unknown package template" new foo bar
test_err "unknown configuration language" new foo .baz
test_err "unknown package template" init foo bar
test_err "unknown configuration language" init foo std.baz

# Test package name validation (should error)
# https://github.com/leanprover/lean4/issues/2637

echo "# TEST: Package name validation"
test_err "illegal package name" new  .
for cmd in new init; do
test_err "illegal package name" $cmd ..
test_err "illegal package name" $cmd ....
test_err "illegal package name" $cmd '  '
test_err "illegal package name" $cmd a/bc
test_err "illegal package name" $cmd a\\b
test_err "reserved package name" $cmd init
test_err "reserved package name" $cmd Lean
test_err "reserved package name" $cmd Lake
test_err "reserved package name" $cmd main
done

# Test default (std) template

echo "# TEST: default template"
test_run new hello .lean
test_run -d hello exe hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello
test_run new hello .toml
test_run -d hello exe hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello

# Test exe template

echo "# TEST: exe template"
test_run new hello exe.lean
test -f hello/Main.lean
test_run -d hello exe hello
rm -rf hello
test_run new hello exe.toml
test -f hello/Main.lean
test_run -d hello exe hello
rm -rf hello

# Test lib template

echo "# TEST: lib template"
test_run new hello lib.lean
test_run -d hello build Hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello
test_run new hello lib.toml
test_run -d hello build Hello
test -f hello/.lake/build/lib/lean/Hello.olean
rm -rf hello

# Test math-lax template

echo "# TEST: math-lax template"
test_run new qed math-lax.lean || true # ignore toolchain download errors
# Remove the require, since we do not wish to download mathlib during tests
sed_i '/^require.*/{N;d;}' qed/lakefile.lean
test_run -d qed build Qed
test -f qed/.lake/build/lib/lean/Qed.olean
rm -rf qed
test_run new qed math-lax.toml || true # ignore toolchain download errors
# Remove the require, since we do not wish to download mathlib during tests
sed_i '/^\[\[require\]\]/{N;N;N;d;}' qed/lakefile.toml
test_run -d qed build Qed
test -f qed/.lake/build/lib/lean/Qed.olean

# Test `init .`

echo "# TEST: init ."
mkdir hello
pushd hello
test_run init .
test_run exe hello
popd

# Test creating packages with uppercase names
# https://github.com/leanprover/lean4/issues/2540

echo "# TEST: Uppercase package names"
test_run new HelloWorld
test_run -d HelloWorld exe helloworld

# Test creating multi-level packages with a `.`

echo "# TEST: Packages with a `.`"
test_run new hello.world
test_run -d hello-world exe hello-world
test -f hello-world/Hello/World/Basic.lean

test_run new hello.exe exe
test_run -d hello-exe exe hello-exe

# Test creating packages with a `-` (i.e., a non-identifier package name)
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

echo "# TEST: Non-identifier package names"
test_run new lean-data
test_run -d lean-data exe lean-data

# Test creating packages starting with digits (i.e., a non-identifier library name)
# https://github.com/leanprover/lean4/issues/2865

echo "# TEST: Non-identifier library names"
test_run new 123-hello
test_run -d 123-hello exe 123-hello

# Test creating packages with components that contain `.`s
# https://github.com/leanprover/lean4/issues/2999

# the unicode name is improperly encoded on windows for non-Lake reasons
if [ "$OSTYPE" != "cygwin" -a "$OSTYPE" != "msys" ]; then
  echo "# TEST: Escaped names"
  test_run new «A.B».«C.D»
  test_run -d A-B-C-D exe a-b-c-d
fi

# Test creating packages with keyword names
# https://github.com/leanprover/lake/issues/128

echo "# TEST: Keyword names"
test_run new meta
test_run -d meta exe meta

# Test `init` with name

echo "# TEST: init <name>"
mkdir hello_world
pushd hello_world
test_run init hello_world exe
test_run exe hello_world
popd

# Test bare `init` on existing package (should error)

echo "# TEST: init existing"
test_err "package already initialized" -d hello_world init

# Test that Mathlib-standard packages have the expected strict linter options.
mkdir mathlib_standards
pushd mathlib_standards
test_run init mathlib_standards math

# Run via elan to make sure the version of Lean is compatible with the version of Mathlib.
ELAN=${ELAN:-elan}

# skip if no elan found
echo "# Check if elan exists"
if ! command -v $ELAN > /dev/null; then
   echo "elan not found; skipping test"
   exit 0
fi

# '#'-commands are not allowed only when enabling the Mathlib standard linters.
echo >MathlibStandards.lean "import Mathlib.Init"
echo >>MathlibStandards.lean "#guard true"
test_cmd_out 'note: this linter can be disabled with `set_option linter.hashCommand false`' $ELAN run $(cat lean-toolchain) lake build mathlib_standards
popd

# Cleanup
rm -f produced.out
