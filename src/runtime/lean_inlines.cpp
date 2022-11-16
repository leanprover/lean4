// generate LLVM IR for `static inline` definitions in lean.h for the LLVM backend
#define static extern // work around clang not emitting code for unused `static` definitions
#include <lean/lean.h>
