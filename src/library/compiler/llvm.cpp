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

// == LLVM <-> Lean: BasicBlockRef ==

static lean_external_class *g_BasicBlock_class = nullptr;

static inline lean_object *BasicBlock_to_lean(LLVMBasicBlockRef s) {
    if (g_BasicBlock_class == nullptr) {
        g_BasicBlock_class =
            lean_register_external_class(donothing_finalize, donothing_foreach);
    }
    return lean_alloc_external(g_BasicBlock_class, s);
}

static inline LLVMBasicBlockRef lean_to_BasicBlock(b_lean_obj_arg s) {
    return static_cast<LLVMBasicBlockRef>(lean_get_external_data(s));
}

// == Array Type <-> C array of types ==

// TODO: there is redundancy here, but I am loath to clean it up with templates,
// because we will somehow dispatch to the correct `lean_to_*` function. I can't
// think of an immediate, clean way to achieve this (plenty of unclean ways. eg:
// create a templated function that we partial template specialize that tells us
// what the correct `lean_to_*` is.
// Concretely: leanToFn<LLVMTypeRef> = lean_to_LLVMType; leanToFn<LLVMValueRef>
// = lean_to_LLVMValue).

// TODO, QUESTION: is there a nicer way to do this?
LLVMTypeRef *array_ref_to_ArrayLLVMType(const lean::array_ref<lean_object *> &arr) {
    const int nargs = arr.size();  // lean::array_size(args);
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMTypeRef *tys = (LLVMTypeRef *)malloc(sizeof(LLVMTypeRef) * nargs);
    for (int i = 0; i < nargs; ++i) {
        tys[i] = lean_to_Type(arr[i]);
        if (LLVM_DEBUG) {
            fprintf(stderr, "... %s ; tys[%d]: %s \n", __PRETTY_FUNCTION__, i,
                    LLVMPrintTypeToString(tys[i]));
        }
    }
    return tys;
}

// TODO, QUESTION: is there a nicer way to do this?
LLVMValueRef *array_ref_to_ArrayLLVMValue(const lean::array_ref<lean_object *> &arr) {
    const int nargs = arr.size();  // lean::array_size(args);
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMValueRef *vals = (LLVMValueRef *)malloc(sizeof(LLVMValueRef) * nargs);
    assert(vals && "unable to allocate array");
    for (int i = 0; i < nargs; ++i) {
        lean_inc(arr[i]); // TODO: do I need this?
        vals[i] = lean_to_Value(arr[i]);
        if (LLVM_DEBUG) {
            fprintf(stderr, "... %s ; vals[%d]: %s \n", __PRETTY_FUNCTION__, i, 
                    LLVMPrintValueToString(vals[i]));
        }
    }
    return vals;
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
    lean_object *retty, lean_object *argtys, uint8_t isvararg,
    lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; retty: %p\n", __PRETTY_FUNCTION__, retty);
        fprintf(stderr, "... %s ; retty: %s \n", __PRETTY_FUNCTION__,
                LLVMPrintTypeToString(lean_to_Type(retty)));
    }
    lean::array_ref<lean_object *> arr(
        argtys, true);  // TODO: why do I need to bump up refcount here?
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; arr.size(): %zu\n", __PRETTY_FUNCTION__,
                arr.size());
    }
    // for 'bool=uint8_t', see 'lean_bool_to_uint64'
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMTypeRef *tys = array_ref_to_ArrayLLVMType(arr);
    LLVMTypeRef out =
        LLVMFunctionType(lean_to_Type(retty), tys, arr.size(), isvararg);
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

extern "C" LEAN_EXPORT lean_object *lean_llvm_void_type_in_context(
    lean_object *ctx, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
    }
    return lean_io_result_mk_ok(
        Type_to_lean(LLVMVoidTypeInContext(lean_to_Context(ctx))));
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
        fprintf(stderr, "%s ; base: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(base)));
    }
    LLVMTypeRef out = LLVMPointerType(lean_to_Type(base), /*addrspace=*/0);
    fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(out));
    return lean_io_result_mk_ok(Type_to_lean(out));
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
    lean_object *ctx, lean_object *fn, lean_object *name, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
        fprintf(stderr, "...%s ; fn: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintValueToString(lean_to_Value(fn)));
        fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
    }
    LLVMBasicBlockRef bb = LLVMAppendBasicBlockInContext(lean_to_Context(ctx), lean_to_Value(fn), lean_string_cstr(name));
    if (LLVM_DEBUG) {
        fprintf(stderr, "...%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
    }
    return lean_io_result_mk_ok(BasicBlock_to_lean(bb));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_position_builder_at_end(
    lean_object *builder, lean_object *bb, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, ".....%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
    }
    LLVMPositionBuilderAtEnd(lean_to_Builder(builder), lean_to_BasicBlock(bb));
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_call2(
    lean_object *builder, lean_object *fnty, lean_object *fnval,
    lean_object *args, lean_object *name, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; fnty: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintTypeToString(lean_to_Type(fnty)));
        fprintf(stderr, "...%s ; fnval: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintValueToString(lean_to_Value(fnval)));
        fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, 
                lean_string_cstr(name));
    }
    lean::array_ref<lean_object *> arr(
        args, true);  // TODO: why do I need to bump up refcount here?
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; arr.size(): %zu\n", __PRETTY_FUNCTION__,
                arr.size());
    }
    LLVMValueRef *arrArgVals = array_ref_to_ArrayLLVMValue(arr);
    LLVMValueRef out = LLVMBuildCall2(
        lean_to_Builder(builder), lean_to_Type(fnty), lean_to_Value(fnval),
        arrArgVals, arr.size(), lean_string_cstr(name));
    free(arrArgVals);
    return lean_io_result_mk_ok(Value_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_build_call(
    lean_object *builder, lean_object *fnval,
    lean_object *args, lean_object *name, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; fnval: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintValueToString(lean_to_Value(fnval)));
        fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, 
                lean_string_cstr(name));
    }
    lean::array_ref<lean_object *> arr(
        args, true);  // TODO: why do I need to bump up refcount here?
    if (LLVM_DEBUG) {
        fprintf(stderr, "... %s ; arr.size(): %zu\n", __PRETTY_FUNCTION__,
                arr.size());
    }
    LLVMValueRef *arrArgVals = array_ref_to_ArrayLLVMValue(arr);
    LLVMValueRef out = LLVMBuildCall(
        lean_to_Builder(builder), lean_to_Value(fnval),
        arrArgVals, arr.size(), lean_string_cstr(name));
    free(arrArgVals);
    return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_cond_br(
    lean_object *builder, lean_object *if_,
    lean_object *thenbb, lean_object *elsebb, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; if_: %s\n", __PRETTY_FUNCTION__,
                LLVMPrintValueToString(lean_to_Value(if_)));
        fprintf(stderr, "...%s ; thenbb: %p\n", __PRETTY_FUNCTION__, thenbb);
        fprintf(stderr, "...%s ; elsebb: %p\n", __PRETTY_FUNCTION__, elsebb);
    }
    LLVMValueRef out = LLVMBuildCondBr(lean_to_Builder(builder), lean_to_Value(if_), lean_to_BasicBlock(thenbb), lean_to_BasicBlock(elsebb));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_br(
    lean_object *builder, lean_object *bb, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
    }
    LLVMValueRef out = LLVMBuildBr(lean_to_Builder(builder), lean_to_BasicBlock(bb));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_store(
    lean_object *builder, lean_object *v, lean_object *slot, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; v: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(v)));
        fprintf(stderr, "...%s ; slot: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(slot)));
    }
    LLVMValueRef out = LLVMBuildStore(lean_to_Builder(builder), lean_to_Value(v), lean_to_Value(slot));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_load(
    lean_object *builder, lean_object *slot, lean_object *name, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; slot: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(slot)));
        fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
    }
    LLVMValueRef out = LLVMBuildLoad(lean_to_Builder(builder), lean_to_Value(slot), lean_string_cstr(name));
    fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_build_alloca(
    lean_object *builder, lean_object *type, lean_object *name, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; ty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(type)));
        fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
    }
    LLVMValueRef out = LLVMBuildAlloca(lean_to_Builder(builder), lean_to_Type(type),lean_string_cstr(name));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ret(
    lean_object *builder, lean_object *v, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
        fprintf(stderr, "...%s ; v: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(v)));
    }
    LLVMValueRef out = LLVMBuildRet(lean_to_Builder(builder), lean_to_Value(v));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ret_void(
    lean_object *builder, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    }
    LLVMValueRef out = LLVMBuildRetVoid(lean_to_Builder(builder));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_unreachable(
    lean_object *builder, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    }
    LLVMValueRef out = LLVMBuildUnreachable(lean_to_Builder(builder));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_get_basic_block_parent(
    lean_object *bb, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
    }
    LLVMValueRef out = LLVMGetBasicBlockParent(lean_to_BasicBlock(bb));
    fprintf(stderr, "...%s ; parent: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
    return lean_io_result_mk_ok(Value_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_get_insert_block(
    lean_object *builder, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    }
    LLVMBasicBlockRef out = LLVMGetInsertBlock(lean_to_Builder(builder));
    return lean_io_result_mk_ok(BasicBlock_to_lean(out));
} 


extern "C" LEAN_EXPORT lean_object *lean_llvm_type_of(lean_object *val, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    }
    LLVMTypeRef ty = LLVMTypeOf(lean_to_Value(val));
    if (LLVM_DEBUG) {
        fprintf(stderr, "...%s ; ty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(ty));
    }
    return lean_io_result_mk_ok(Type_to_lean(ty));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_print_module_to_string(lean_object *mod, lean_object* /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; module: %p\n", __PRETTY_FUNCTION__, mod);
    }
    const char *s = LLVMPrintModuleToString(lean_to_Module(mod));
    return lean_io_result_mk_ok(lean::mk_string(s));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_int(lean_object *ty, uint64_t val, uint8_t sext, lean_object * /* w */) {
    if (LLVM_DEBUG) {
        fprintf(stderr, "%s ; ty: %p\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(ty)));
        fprintf(stderr, "...%s ; val: %lu\n", __PRETTY_FUNCTION__, val);
        fprintf(stderr, "...%s ; sext: %d\n", __PRETTY_FUNCTION__, (int)sext);
    }
    LLVMValueRef out = LLVMConstInt(lean_to_Type(ty), val, sext);
    return lean_io_result_mk_ok(Value_to_lean(out));
}
