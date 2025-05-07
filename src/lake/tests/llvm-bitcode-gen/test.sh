#!/usr/bin/env bash
source ../common.sh

./clean.sh

test_run update

# Skip test if we don't have LLVM backend in the Lean toolchain
echo "# Check if LLVM enabled"
if [[ ! $($LAKE env lean --features) =~ LLVM ]]; then
  echo "Skipping test: 'lean' does not have LLVM backend enabled"
  exit 0
fi

echo "# TESTS"
test_out "Main.bc.o" build -v  # check that we build using the bitcode object file.

# If we have the LLVM backend, check that the `lakefile.lean` is aware of this.
test_out "true" script run llvm-bitcode-gen/hasLLVMBackend

# If we have the LLVM backend in the Lean toolchain, then we expect this to
# print `true`, as this queries the same flag that Lake queries to check the presence
# of the LLVM toolchian.
test_out -q exe llvm-bitcode-gen | grep --color true

# If we have the LLVM backend, check that lake builds bitcode artefacts.
test -f .lake/build/ir/LlvmBitcodeGen.bc
test -f .lake/build/ir/Main.bc

# cleanup
rm -f produced.out
