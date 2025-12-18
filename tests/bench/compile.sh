#!/usr/bin/env bash
source ../common.sh

compile_lean_c_backend
# Then check the LLVM version
if lean_has_llvm_support; then
  echo "running LLVM program..."
  compile_lean_llvm_backend
fi
