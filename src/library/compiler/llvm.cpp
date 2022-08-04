/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Siddharth Bhat

This file contains bare bones bindings to the LLVM C FFI. This enables
`src/Lean/Compiler/IR/EmitLLVM.lean` to produce LLVM bitcode from
Lean's IR.
*/

#include "runtime/string_ref.h"
#include <lean/lean.h>
#include <llvm-c/Core.h>
#include <llvm-c/BitWriter.h>

static void donothing_finalize(void * obj) {
    // delete static_cast<S*>(obj);
}

static void donothing_foreach(void *, b_lean_obj_arg) {
    // do nothing since `S` does not contain nested Lean objects
}

// == LLVM <-> Lean: ModuleRef ==

static lean_external_class * g_Module_class = nullptr;

static inline lean_object * Module_to_lean(LLVMModuleRef s) {
    if (g_Module_class == nullptr) {
        g_Module_class = lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Module_class, s);
}

static inline LLVMModuleRef lean_to_Module(b_lean_obj_arg s) {
    return static_cast<LLVMModuleRef>(lean_get_external_data(s));
}

// == LLVM <-> Lean: ContextRef ==

static lean_external_class * g_Context_class = nullptr;

static inline lean_object * Context_to_lean(LLVMContextRef s) {
    if (g_Context_class == nullptr) {
        g_Context_class = lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Context_class, s);
}

static inline LLVMContextRef lean_to_Context(b_lean_obj_arg s) {
    return static_cast<LLVMContextRef>(lean_get_external_data(s));
}


// static lean_external_class *g_llvm_context_external_class = NULL;
// static void llvm_context_finalizer(void *h) {}
// static void llvm_context_foreach(void *mod, b_lean_obj_arg fn) {}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_context(lean_object * /* w */) {
    LLVMContextRef ctx = LLVMContextCreate();
    fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
    return lean_io_result_mk_ok(Context_to_lean(ctx));
};

// opaque createModule (ctx: @&Ptr Context) (name: @&String): IO (Ptr Module)
extern "C" LEAN_EXPORT lean_object *lean_llvm_create_module(lean_object *ctx, lean_object *str, lean_object * /* w */) {
    fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);

    LLVMModuleRef mod = LLVMModuleCreateWithNameInContext(lean::string_ref(str).data(),
                                                         lean_to_Context(ctx));
    LLVMWriteBitcodeToFile(mod, "/home/bollu/temp/module.bc");
    fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);

    return lean_io_result_mk_ok(Module_to_lean(mod));
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_write_bitcode_to_file(
    lean_object *mod, lean_object *filepath, lean_object * /* w */) {

    const char *filepath_str = lean::string_ref(filepath).data();
    int err = LLVMWriteBitcodeToFile(lean_to_Module(mod), filepath_str);
    std::cerr << "wrote bitcode.\n";

    assert(!err && "unable to write bitcode");
    // IO Unit
    return lean_io_result_mk_ok(lean_box(0));
};


extern "C" LEAN_EXPORT lean_object *lean_llvm_module_to_string(
    lean_object *mod, lean_object * /* w */) {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    return lean_io_result_mk_ok(
        lean_mk_string(LLVMPrintModuleToString((LLVMModuleRef)mod)));
};

