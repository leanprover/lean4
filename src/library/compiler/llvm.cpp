/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Siddharth Bhat

This file contains bare bones bindings to the LLVM C FFI. This enables
`src/Lean/Compiler/IR/EmitLLVM.lean` to produce LLVM bitcode from
Lean's IR.
*/

#include <lean/lean.h>
#include <llvm-c/BitWriter.h>
#include <llvm-c/Core.h>

#include "runtime/array_ref.h"
#include "runtime/string_ref.h"

#define LLVM_DEBUG 1

static void donothing_finalize(void *obj) {
    (void)obj;
    // delete static_cast<S*>(obj);
}

static void donothing_foreach(void *, b_lean_obj_arg) {
    // do nothing since `S` does not contain nested Lean objects
}

// == LLVM <-> Lean: ModuleRef ==

static lean_external_class *g_Module_class = nullptr;

static inline lean_object *Module_to_lean(LLVMModuleRef s) {
    if (g_Module_class == nullptr) {
        g_Module_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Module_class, s);
}

static inline LLVMModuleRef lean_to_Module(b_lean_obj_arg s) {
    return static_cast<LLVMModuleRef>(lean_get_external_data(s));
}

// == LLVM <-> Lean: ContextRef ==

static lean_external_class *g_Context_class = nullptr;

static inline lean_object *Context_to_lean(LLVMContextRef s) {
    if (g_Context_class == nullptr) {
        g_Context_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Context_class, s);
}

static inline LLVMContextRef lean_to_Context(b_lean_obj_arg s) {
    return static_cast<LLVMContextRef>(lean_get_external_data(s));
}

// == LLVM <-> Lean: TypeRef ==

static lean_external_class *g_Type_class = nullptr;

static inline lean_object *Type_to_lean(LLVMTypeRef s) {
    if (g_Type_class == nullptr) {
        g_Type_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Type_class, s);
}

static inline LLVMTypeRef lean_to_Type(b_lean_obj_arg s) {
    return static_cast<LLVMTypeRef>(lean_get_external_data(s));
}

// == LLVM <-> Lean: ValueRef ==

static lean_external_class *g_Value_class = nullptr;

static inline lean_object *Value_to_lean(LLVMValueRef s) {
    if (g_Value_class == nullptr) {
        g_Value_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Value_class, s);
}

static inline LLVMValueRef lean_to_Value(b_lean_obj_arg s) {
    return static_cast<LLVMValueRef>(lean_get_external_data(s));
}

// == LLVM <-> Lean: BuilderRef ==

static lean_external_class *g_Builder_class = nullptr;

static inline lean_object *Builder_to_lean(LLVMBuilderRef s) {
    if (g_Builder_class == nullptr) {
        g_Builder_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_Builder_class, s);
}

static inline LLVMBuilderRef lean_to_Builder(b_lean_obj_arg s) {
    return static_cast<LLVMBuilderRef>(lean_get_external_data(s));
}

// == FFI ==
// static lean_external_class *g_llvm_context_external_class = NULL;
// static void llvm_context_finalizer(void *h) {}
// static void llvm_context_foreach(void *mod, b_lean_obj_arg fn) {}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_context(
    lean_object * /* w */) {
    LLVMContextRef ctx = LLVMContextCreate();
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
    }
    return lean_io_result_mk_ok(Context_to_lean(ctx));
};

// opaque createModule (ctx: @&Ptr Context) (name: @&String): IO (Ptr Module)
extern "C" LEAN_EXPORT lean_object *lean_llvm_create_module(
    lean_object *ctx, lean_object *str, lean_object * /* w */) {
    LLVMModuleRef mod = LLVMModuleCreateWithNameInContext(
        lean::string_ref(str).data(), lean_to_Context(ctx));
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
    }
    // LLVMWriteBitcodeToFile(mod, "/home/bollu/temp/module.bc");
    return lean_io_result_mk_ok(Module_to_lean(mod));
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_write_bitcode_to_file(
    lean_object *mod, lean_object *filepath, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
    }
    const int err =
        LLVMWriteBitcodeToFile(lean_to_Module(mod), lean_string_cstr(filepath));
    assert(!err && "unable to write bitcode");
    return lean_io_result_mk_ok(lean_box(0));  // IO Unit
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_module_to_string(
    lean_object *mod, lean_object * /* w */) {
    // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
    }
    return lean_io_result_mk_ok(
        lean_mk_string(LLVMPrintModuleToString((LLVMModuleRef)mod)));
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_function(
    lean_object *mod, lean_object *name, lean_object *type,
    lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; lean_llvm_add_function: %p\n",
                __PRETTY_FUNCTION__, mod);
    }
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; name: %s \n", __PRETTY_FUNCTION__,
                lean_string_cstr(name));
    }
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; type: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintTypeToString(lean_to_Type(type)));
    }
    return lean_io_result_mk_ok(Value_to_lean(LLVMAddFunction(
        lean_to_Module(mod), lean_string_cstr(name), lean_to_Type(type))));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_named_function(
    lean_object *mod, lean_object *name, lean_object * /* w */) {
    LLVMValueRef f =
        LLVMGetNamedFunction(lean_to_Module(mod), lean_string_cstr(name));
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; name: %s\n", __PRETTY_FUNCTION__,
                lean_string_cstr(name));
    }
    if (LLVM_DEBUG) {
        fprintf(stderr, "...%s ; f: %p\n", __PRETTY_FUNCTION__, f);
    }
    return lean_io_result_mk_ok(f ? lean::mk_option_some(Value_to_lean(f))
                                  : lean::mk_option_none());
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_global(
    lean_object *mod, lean_object *name, lean_object *type,
    lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
    }
    return lean_io_result_mk_ok(Value_to_lean(LLVMAddGlobal(
        lean_to_Module(mod), lean_to_Type(type), lean_string_cstr(name))));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_named_global(
    lean_object *mod, lean_object *name, lean_object * /* w */) {
    LLVMValueRef g =
        LLVMGetNamedGlobal(lean_to_Module(mod), lean_string_cstr(name));
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; g: %p\n", __PRETTY_FUNCTION__, g);
    }
    return lean_io_result_mk_ok(g ? lean::mk_option_some(Value_to_lean(g))
                                  : lean::mk_option_none());
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_function_type(
    lean_object *retty, lean_object *args, uint8_t isvararg,
    lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; retty: %p\n", __PRETTY_FUNCTION__, retty);
    }
    lean::array_ref<lean_object *> arr(args, true); // TODO: why do I need to bump up refcount here?
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; retty: %s \n", __PRETTY_FUNCTION__,
                LLVMPrintTypeToString(lean_to_Type(retty)));
    }
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; arr.size(): %zu\n", __PRETTY_FUNCTION__,
                arr.size());
    }

    // for 'bool=uint8_t', see 'lean_bool_to_uint64'
    const int nargs = arr.size();  // lean::array_size(args);
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMTypeRef *tys = (LLVMTypeRef *)malloc(sizeof(LLVMTypeRef) * nargs);
    for (int i = 0; i < nargs; ++i) {
        tys[i] = lean_to_Type(arr[i]);
        if (LLVM_DEBUG) {
            fprintf(stderr, "... %s ; tys[i]: %s \n", __PRETTY_FUNCTION__,
                    LLVMPrintTypeToString(tys[i]));
        }
    }
    LLVMTypeRef out =
        LLVMFunctionType(lean_to_Type(retty), tys, nargs, isvararg);
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; out: %s \n", __PRETTY_FUNCTION__,
                LLVMPrintTypeToString(out));
    }
    free(tys);
    return lean_io_result_mk_ok(Type_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_int_type_in_context(
    lean_object *ctx, uint64_t width, lean_object * /* w */) {
    // bollu, TODO: Check that this actually works.
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; %lu \n", __PRETTY_FUNCTION__, width);
    }
    return lean_io_result_mk_ok(
        Type_to_lean(LLVMIntTypeInContext(lean_to_Context(ctx), width)));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_float_type_in_context(
    lean_object *ctx, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
    }
    return lean_io_result_mk_ok(
        Type_to_lean(LLVMFloatTypeInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_double_type_in_context(
    lean_object *ctx, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
    }
    return lean_io_result_mk_ok(
        Type_to_lean(LLVMDoubleTypeInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_pointer_type(
    lean_object *base, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; base: %p\n", __PRETTY_FUNCTION__, base);
    }
    return lean_io_result_mk_ok(
        Type_to_lean(LLVMPointerType(lean_to_Type(base), /*addrspace=*/0)));
}


extern "C" LEAN_EXPORT lean_object *lean_llvm_create_builder_in_context(
    lean_object *ctx, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
    }
    return lean_io_result_mk_ok(
        Builder_to_lean(LLVMCreateBuilderInContext(lean_to_Context(ctx))));
}



extern "C" LEAN_EXPORT lean_object *lean_llvm_append_basic_block_in_context(
    lean_object *ctx, lean_object *fn, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
        fprintf(stderr, "...%s ; fn: %p\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(fn)));
    }
    return lean_io_result_mk_ok(
        Builder_to_lean(LLVMCreateBuilderInContext(lean_to_Context(ctx))));
}


