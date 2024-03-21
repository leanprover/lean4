#!/usr/bin/env bash
set -euxo pipefail

LAKE=${LAKE:-../../build/bin/lake}

./clean.sh

# Skip test if we don't have LLVM backend in the Lean toolchain
if [[ ! $(lean --features) =~ LLVM ]]; then
  echo "Skipping test: 'lean' does not have LLVM backend enabled"
  exit 0
fi

$LAKE update
$LAKE build -v | grep "Main.bc.o" # check that we build using the bitcode object file.

# If we have the LLVM backend, check that the `lakefile.lean` is aware of this.
lake script run llvm-bitcode-gen/hasLLVMBackend | grep "true"

# If we have the LLVM backend in the Lean toolchain, then we expect this to
# print `true`, as this queries the same flag that Lake queries to check the presence
# of the LLVM toolchian.
./.lake/build/bin/llvm-bitcode-gen | grep 'true'

# If we have the LLVM backend, check that lake builds bitcode artefacts.
test -f .lake/build/ir/LlvmBitcodeGen.bc
test -f .lake/build/ir/Main.bc
