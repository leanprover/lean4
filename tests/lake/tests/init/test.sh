#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Ensure that Lake is run without a toolchain name
# (for consistent default behavior in tests)
export ELAN_TOOLCHAIN=

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

test_std() {
  local pkg=$1; local mod=$2; local exe=${3:-$1}
  test_exp -f $pkg/Main.lean
  test_exp -f $pkg/$mod.lean
  test_exp -f $pkg/$mod/Basic.lean
  test_run -d $pkg exe $exe
  test_exp -f $pkg/.lake/build/lib/lean/$mod.olean
}

echo "# TEST: default template"
test_run new hello .lean
test_std hello Hello
rm -rf hello
test_run new hello .toml
test_std hello Hello
rm -rf hello

# Test exe template

test_exe() {
  local pkg=$1; local mod=${2:-$1}; local exe=${3:-$1}
  test_exp ! -d $pkg/$mod
  test_exp -f $pkg/Main.lean
  test_run -d $pkg exe $exe
}

echo "# TEST: exe template"
test_run new hello exe.lean
test_exe hello Hello
rm -rf hello
test_run new hello exe.toml
test_exe hello Hello
rm -rf hello

# Test lib template

test_lib() {
  local pkg=$1; local mod=$2
  test_exp -f $pkg/$mod.lean
  test_exp -f $pkg/$mod/Basic.lean
  test_exp ! -f $pkg/Main.lean
  test_run -d $pkg build $mod
  test_exp -f $pkg/.lake/build/lib/lean/$mod.olean
}

echo "# TEST: lib template"
test_run new hello lib.lean
test_lib hello Hello
rm -rf hello
test_run new hello lib.toml
test_lib hello Hello
rm -rf hello

# Test math & math-lax template

test_math_tmp () {
  local tmp=$1; local pkg=$2; local mod=$3
  echo "# TEST: $tmp template"
  # Use `--offline` and remove the `require`,
  # since we do not wish to download mathlib during tests
  ELAN_TOOLCHAIN="v4.0.0-test" test_run new $pkg $tmp.lean --offline
  sed_i '/^require.*/{N;d;}' $pkg/lakefile.lean
  test_cmd_out "v4.0.0-test" cat $pkg/lean-toolchain
  test_lib $pkg $mod
  rm -rf $pkg
  # Use `--offline` and remove the `require`,
  # since we do not wish to download mathlib during tests
  test_out "creating a new math package with a non-release Lean toolchain" \
    new $pkg $tmp.toml --offline
  sed_i '/^\[\[require\]\]/{N;N;N;d;}' $pkg/lakefile.toml
  test_lib $pkg $mod
}

test_math_tmp math-lax qed-lax QedLax
test_math_tmp math qed Qed

# Test `init .`

echo "# TEST: init ."
mkdir hello
pushd hello
test_run init .
test_std . Hello hello
popd

# Test creating packages with uppercase names
# https://github.com/leanprover/lean4/issues/2540

echo "# TEST: Uppercase package names"
test_run new HelloWorld
test_std HelloWorld HelloWorld helloworld

# Test creating multi-level packages with a `.`

echo "# TEST: Packages with a `.`"
test_run new hello.world
test_std hello-world Hello/World

test_run new hello.exe exe
test_exe hello-exe Hello

# Test creating packages with a `-` (i.e., a non-identifier package name)
# https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/lake.20new.20lean-data

echo "# TEST: Non-identifier package names"
test_run new lean-data
test_std lean-data LeanData

# Test creating packages starting with digits (i.e., a non-identifier library name)
# https://github.com/leanprover/lean4/issues/2865

echo "# TEST: Non-identifier library names"
test_run new 123-hello
test_std 123-hello 123Hello

# Test creating packages with components that contain `.`s
# https://github.com/leanprover/lean4/issues/2999

# the unicode name is improperly encoded on windows for non-Lake reasons
if [ "$OSTYPE" != "cygwin" -a "$OSTYPE" != "msys" ]; then
  echo "# TEST: Escaped names"
  test_run new «A.B».«C.D»
  test_std A-B-C-D A.B/C.D a-b-c-d
fi

# Test creating packages with keyword names
# https://github.com/leanprover/lake/issues/128

echo "# TEST: Keyword names"
test_run new meta
test_std meta Meta

# Test `init` with name

echo "# TEST: init <name>"
mkdir hello_world
pushd hello_world
test_run init hello_world exe
test_exe . HelloWorld hello_world
popd

# Test bare `init` on existing package (should error)

echo "# TEST: init existing"
test_err "package already initialized" -d hello_world init

# Cleanup
rm -f produced.out
