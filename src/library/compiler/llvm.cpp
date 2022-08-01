/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Siddharth Bhat

This file contains bare bones bindings to the LLVM C FFI. This enables
`src/Lean/Compiler/IR/EmitLLVM.lean` to produce LLVM bitcode from
Lean's IR.
*/

#include <lean/lean.h>
#include <llvm-c/Core.h>

// static lean_external_class *g_llvm_context_external_class = NULL;
// static void llvm_context_finalizer(void *h) {}
// static void llvm_context_foreach(void *mod, b_lean_obj_arg fn) {}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_context() {
    return lean_io_result_mk_ok((lean_object *)LLVMContextCreate());
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_module(lean_object *ctx) {
    return lean_io_result_mk_ok(
        (lean_object *)LLVMModuleCreateWithNameInContext("foo",
                                                         (LLVMContextRef)ctx));
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_module_to_string(
    lean_object *mod) {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    return lean_io_result_mk_ok(
        lean_mk_string(LLVMPrintModuleToString((LLVMModuleRef)mod)));
};

// static void initialize_process() {
//     g_llvm_context_external_class = lean_register_external_class(
//         llvm_context_finalizer, llvm_context_foreach);
// }
// static void finalize_process() {}

