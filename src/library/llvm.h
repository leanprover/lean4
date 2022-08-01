/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Siddharth Bhat

This file contains bare bones bindings to the LLVM C FFI. This enables
`src/Lean/Compiler/IR/EmitLLVM.lean` to produce LLVM bitcode from
Lean's IR.
*/

#pragma once
#include <lean/lean.h>
#include <llvm-c/Core.h>

static lean_external_class *g_llvm_context_external_class = NULL;

static void llvm_context_finalizer(void *h) {}

static void llvm_context_foreach(void *mod, b_lean_obj_arg fn) {}

// struct S {
//     unsigned    m_x;
//     unsigned    m_y;
//     std::string m_s;
//     S(unsigned x, unsigned y, char const * s):m_x(x), m_y(y), m_s(s) {}
// };
//
// static void S_finalize(void * obj) {
//     delete static_cast<S*>(obj);
// }
//
// static void S_foreach(void *, b_lean_obj_arg) {
//     // do nothing since `S` does not contain nested Lean objects
// }
//
// static lean_external_class * g_S_class = nullptr;
//
// static inline lean_object * S_to_lean(S * s) {
//     if (g_S_class == nullptr) {
//         g_S_class = lean_register_external_class(S_finalize, S_foreach);
//     }
//     return lean_alloc_external(g_S_class, s);
// }
//
// static inline S const * to_S(b_lean_obj_arg s) {
//     return static_cast<S *>(lean_get_external_data(s));
// }
//
// extern "C" LEAN_EXPORT lean_object * lean_mk_S(uint32_t x, uint32_t y,
// b_lean_obj_arg s) {
//     return S_to_lean(new S(x, y, lean_string_cstr(s)));
// }
//
// extern "C" LEAN_EXPORT uint32_t lean_S_add_x_y(b_lean_obj_arg s) {
//     return to_S(s)->m_x + to_S(s)->m_y;
// }
//
// extern "C" LEAN_EXPORT lean_object * lean_S_string(b_lean_obj_arg s) {
//     return lean_mk_string(to_S(s)->m_s.c_str());
// }
//
// static S g_s(0, 0, "");
//
// extern "C" LEAN_EXPORT lean_object * lean_S_global_append(b_lean_obj_arg str,
// lean_object /* w */) {
//     g_s.m_s += lean_string_cstr(str);
//     return lean_io_result_mk_ok(lean_box(0));
// }
//
// extern "C" LEAN_EXPORT lean_object * lean_S_global_string(lean_object /* w
// */) {
//     return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
// }
//
// extern "C" LEAN_EXPORT lean_object * lean_S_update_global(b_lean_obj_arg s,
// lean_object /* w */) {
//     g_s.m_x = to_S(s)->m_x;
//     g_s.m_y = to_S(s)->m_y;
//     g_s.m_s = to_S(s)->m_s;
//     return lean_io_result_mk_ok(lean_box(0));
// }

LEAN_EXPORT lean_object *lean_llvm_create_context() {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    return lean_io_result_mk_ok(
        (lean_object *)LLVMContextCreate());  // lean_mk_string(g_s.m_s.c_str()));
};

LEAN_EXPORT lean_object *lean_llvm_create_module(lean_object *ctx) {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    return lean_io_result_mk_ok((lean_object *)LLVMModuleCreateWithNameInContext(
        "foo", (LLVMContextRef)ctx));  // lean_mk_string(g_s.m_s.c_str()));
};

LEAN_EXPORT lean_object *lean_llvm_module_to_string(lean_object *mod) {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    return lean_io_result_mk_ok(
        lean_mk_string(LLVMPrintModuleToString((LLVMModuleRef)mod)));
    // return lean_io_result_mk_ok((void *)LLVMModuleCreateNameInContext("foo",
    // (LLVMContextRef)ctx)); //lean_mk_string(g_s.m_s.c_str()));
};

void initialize_process() {
    g_llvm_context_external_class = lean_register_external_class(
        llvm_context_finalizer, llvm_context_foreach);
}
void finalize_process() {}

