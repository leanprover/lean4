/*
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Siddharth Bhat

This file contains bare bones bindings to the LLVM C FFI. This enables
`src/Lean/Compiler/IR/EmitLLVM.lean` to produce LLVM bitcode from
Lean's IR.
*/

#include <lean/lean.h>

#include <cassert>

#include "runtime/array_ref.h"
#include "runtime/debug.h"
#include "runtime/string_ref.h"

#ifdef LEAN_LLVM
#include "llvm-c/BitReader.h"
#include "llvm-c/BitWriter.h"
#include "llvm-c/Core.h"
#include "llvm-c/Linker.h"
#include "llvm-c/Target.h"
#include "llvm-c/TargetMachine.h"
#include "llvm-c/Types.h"
#include "llvm-c/Transforms/PassBuilder.h"
#include "llvm-c/Transforms/PassManagerBuilder.h"
#endif

// This is mostly boilerplate, suppress warnings
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

extern "C" LEAN_EXPORT lean_object* lean_llvm_initialize_target_info(lean_object * /* w */) {

#ifdef LEAN_LLVM
    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargets();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllAsmParsers();
    LLVMInitializeAllAsmPrinters();
#endif

    return lean_io_result_mk_ok(lean_box(0));
}

#ifdef LEAN_LLVM
// == LLVM <-> Lean: Target ==
static inline size_t Target_to_lean(LLVMTargetRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMTargetRef lean_to_Target(size_t s) {
    return reinterpret_cast<LLVMTargetRef>(s);
}

// == LLVM <-> Lean: TargetMachine ==

static inline size_t TargetMachine_to_lean(LLVMTargetMachineRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMTargetMachineRef lean_to_TargetMachine(size_t s) {
    return reinterpret_cast<LLVMTargetMachineRef>(s);
}

// == LLVM <-> Lean: MemoryBuffer ==

static inline size_t MemoryBuffer_to_lean(LLVMMemoryBufferRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMMemoryBufferRef lean_to_MemoryBuffer(size_t s) {
    return reinterpret_cast<LLVMMemoryBufferRef>(s);
}

// == LLVM <-> Lean: ModuleRef ==

static inline size_t Module_to_lean(LLVMModuleRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMModuleRef lean_to_Module(size_t s) {
    return reinterpret_cast<LLVMModuleRef>(s);
}

// == LLVM <-> Lean: ContextRef ==
static inline size_t Context_to_lean(LLVMContextRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMContextRef lean_to_Context(size_t s) {
    return reinterpret_cast<LLVMContextRef>(s);
}

// == LLVM <-> Lean: TypeRef ==
static inline size_t Type_to_lean(LLVMTypeRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMTypeRef lean_to_Type(size_t s) {
    return reinterpret_cast<LLVMTypeRef>(s);
}

// == LLVM <-> Lean: ValueRef ==
static inline size_t Value_to_lean(LLVMValueRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMValueRef lean_to_Value(size_t s) {
    return reinterpret_cast<LLVMValueRef>(s);
}

// == LLVM <-> Lean: BuilderRef ==
static inline size_t Builder_to_lean(LLVMBuilderRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMBuilderRef lean_to_Builder(size_t s) {
    return reinterpret_cast<LLVMBuilderRef>(s);
}

// == LLVM <-> Lean: BasicBlockRef ==
static inline size_t BasicBlock_to_lean(LLVMBasicBlockRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMBasicBlockRef lean_to_BasicBlock(size_t s) {
    return reinterpret_cast<LLVMBasicBlockRef>(s);
}

// == LLVM <-> Lean: PassManagerRef ==
static inline size_t PassManager_to_lean(LLVMPassManagerRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMPassManagerRef lean_to_PassManager(size_t s) {
    return reinterpret_cast<LLVMPassManagerRef>(s);
}

// == LLVM <-> Lean: PassManagerRef ==
static inline size_t PassManagerBuilder_to_lean(LLVMPassManagerBuilderRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMPassManagerBuilderRef lean_to_PassManagerBuilder(size_t s) {
    return reinterpret_cast<LLVMPassManagerBuilderRef>(s);
}

// == LLVM <-> Lean: AttributeRef ==
static inline size_t Attribute_to_lean(LLVMAttributeRef s) {
    return reinterpret_cast<size_t>(s);
}

static inline LLVMAttributeRef lean_to_Attribute(size_t s) {
    return reinterpret_cast<LLVMAttributeRef>(s);
}
#else
typedef int LLVMBasicBlockRef;
typedef int LLVMContextRef;
typedef int LLVMBuilderRef;
typedef int LLVMTargetRef;
typedef int LLVMTargetMachineRef;
typedef int LLVMTypeRef;
typedef int LLVMValueRef;
typedef int LLVMModuleRef;
typedef int LLVMPassManagerRef;
typedef int LLVMPassManagerBuilderRef;
#endif  // LEAN_LLVM

// == Array Type <-> C array of types ==

// There is redundancy here, but I am loath to clean it up with templates,
// because we will somehow dispatch to the correct `lean_to_*` function. I can't
// think of an immediate, clean way to achieve this (plenty of unclean ways. eg:
// create a templated function that we partial template specialize that tells us
// what the correct `lean_to_*` is.
// Concretely:
//  leanToFn<LLVMTypeRef> = lean_to_LLVMType;
//  leanToFn<LLVMValueRef> = lean_to_LLVMValue).
LLVMTypeRef *array_ref_to_ArrayLLVMType(
    const lean::array_ref<lean_object *> &arr) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    const int nargs = arr.size();  // lean::array_size(args);
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMTypeRef *tys = (LLVMTypeRef *)malloc(sizeof(LLVMTypeRef) * nargs);
    for (int i = 0; i < nargs; ++i) {
        tys[i] = lean_to_Type(lean_unbox_usize(arr[i]));
    }
    return tys;
#endif  // LEAN_LLVM
}

// TODO: Is there a nicer way to do this?
LLVMValueRef *array_ref_to_ArrayLLVMValue(
    const lean::array_ref<lean_object *> &arr) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    const int nargs = arr.size();  // lean::array_size(args);
    // bollu: ouch, this is expensive! There must be a cheaper way?
    LLVMValueRef *vals = (LLVMValueRef *)malloc(sizeof(LLVMValueRef) * nargs);
    lean_always_assert(vals && "unable to allocate array");
    for (int i = 0; i < nargs; ++i) {
        lean_inc(arr[i]);  // TODO: do I need this?
        vals[i] = lean_to_Value(lean_unbox_usize(arr[i]));
    }
    return vals;
#endif  // LEAN_LLVM
}

// == FFI ==
extern "C" LEAN_EXPORT lean_object *lean_llvm_create_context(
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMContextRef ctx = LLVMContextCreate();
    return lean_io_result_mk_ok(lean_box_usize(Context_to_lean(ctx)));
#endif  // LEAN_LLVM
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_module(
    size_t ctx, lean_object *str, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMModuleRef mod = LLVMModuleCreateWithNameInContext(lean_string_cstr(str),
                                                          lean_to_Context(ctx));
    return lean_io_result_mk_ok(lean_box_usize(Module_to_lean(mod)));
#endif  // LEAN_LLVM
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_write_bitcode_to_file(size_t ctx,
    size_t mod, lean_object *filepath, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    const int err =
        LLVMWriteBitcodeToFile(lean_to_Module(mod), lean_string_cstr(filepath));
    lean_always_assert(!err && "unable to write bitcode");
    return lean_io_result_mk_ok(lean_box(0));  // IO Unit
#endif  // LEAN_LLVM
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_module_to_string(
    size_t ctx, size_t mod, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    char *str = LLVMPrintModuleToString(lean_to_Module(mod));
    lean_object *out =  lean_io_result_mk_ok(lean_mk_string(str));
    free(str);
    return out;
#endif  // LEAN_LLVM
};

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_function(
    size_t ctx, size_t mod, lean_object *name, size_t type, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMAddFunction(
        lean_to_Module(mod), lean_string_cstr(name), lean_to_Type(type));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_named_function(
    size_t ctx, size_t mod, lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef f =
        LLVMGetNamedFunction(lean_to_Module(mod), lean_string_cstr(name));
    return lean_io_result_mk_ok(
        f ? lean::mk_option_some(lean_box_usize(Value_to_lean(f)))
          : lean::mk_option_none());
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_global(
    size_t ctx, size_t mod, lean_object *name, size_t type, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMAddGlobal(lean_to_Module(mod), lean_to_Type(type),
                                     lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_named_global(
    size_t ctx, size_t mod, lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef g =
        LLVMGetNamedGlobal(lean_to_Module(mod), lean_string_cstr(name));
    return lean_io_result_mk_ok(
        g ? lean::mk_option_some(lean_box_usize(Value_to_lean(g)))
          : lean::mk_option_none());
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_global_string(
    size_t ctx, size_t builder, lean_object *str, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    lean::string_ref sref = lean::string_ref(str, true);
    lean::string_ref nameref = lean::string_ref(name, true);
    LLVMValueRef out = LLVMBuildGlobalString(lean_to_Builder(builder),
                                             sref.data(), nameref.data());
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}
extern "C" LEAN_EXPORT lean_object *lean_llvm_get_undef(size_t ctx, size_t ty,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetUndef(lean_to_Type(ty));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_set_initializer(
    size_t ctx, size_t global, size_t initializer, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMSetInitializer(lean_to_Value(global), lean_to_Value(initializer));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_function_type(
    size_t ctx, size_t retty, lean_object *argtys, uint8_t isvararg,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    lean::array_ref<lean_object *> arr(argtys, true);
    // TODO, this is expensive! Is there a cheaper way?
    LLVMTypeRef *tys = array_ref_to_ArrayLLVMType(arr);
    LLVMTypeRef out =
        LLVMFunctionType(lean_to_Type(retty), tys, arr.size(), isvararg);
    free(tys);
    return lean_io_result_mk_ok(lean_box_usize(Type_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_opaque_pointer_type_in_context(
    size_t ctx, uint64_t addrspace, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Type_to_lean(LLVMPointerTypeInContext(lean_to_Context(ctx), addrspace))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_int_type_in_context(
    size_t ctx, uint64_t width, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Type_to_lean(LLVMIntTypeInContext(lean_to_Context(ctx), width))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_float_type_in_context(
    size_t ctx, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Type_to_lean(LLVMFloatTypeInContext(lean_to_Context(ctx)))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_void_type_in_context(
    size_t ctx, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Type_to_lean(LLVMVoidTypeInContext(lean_to_Context(ctx)))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_double_type_in_context(
    size_t ctx, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Type_to_lean(LLVMDoubleTypeInContext(lean_to_Context(ctx)))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_pointer_type(
    size_t ctx, size_t base, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMTypeRef out = LLVMPointerType(lean_to_Type(base), /*addrspace=*/0);
    return lean_io_result_mk_ok(lean_box_usize(Type_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_array_type(
    size_t ctx, size_t base, uint64_t nelem, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMTypeRef out = LLVMArrayType(lean_to_Type(base), /*nelem=*/nelem);
    return lean_io_result_mk_ok(lean_box_usize(Type_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_builder_in_context(
    size_t ctx, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(
        Builder_to_lean(LLVMCreateBuilderInContext(lean_to_Context(ctx)))));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_append_basic_block_in_context(
    size_t ctx, size_t fn, lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMBasicBlockRef bb = LLVMAppendBasicBlockInContext(
        lean_to_Context(ctx), lean_to_Value(fn), lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_usize(BasicBlock_to_lean(bb)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_position_builder_at_end(
    size_t ctx, size_t builder, size_t bb, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMPositionBuilderAtEnd(lean_to_Builder(builder), lean_to_BasicBlock(bb));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_clear_insertion_position(size_t ctx,
    size_t builder, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMClearInsertionPosition(lean_to_Builder(builder));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_call2(
    size_t ctx, size_t builder, size_t fnty, size_t fnval, lean_object *args,
    lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    lean::array_ref<lean_object *> arr(args, true);
    LLVMValueRef *arrArgVals = array_ref_to_ArrayLLVMValue(arr);

    LLVMValueRef out = LLVMBuildCall2(
        lean_to_Builder(builder), lean_to_Type(fnty), lean_to_Value(fnval),
        arrArgVals, arr.size(), lean_string_cstr(name));
    free(arrArgVals);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_cond_br(
    size_t ctx,
    size_t builder, size_t if_, size_t thenbb, size_t elsebb,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildCondBr(lean_to_Builder(builder), lean_to_Value(if_),
                        lean_to_BasicBlock(thenbb), lean_to_BasicBlock(elsebb));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_br(size_t ctx, size_t builder,
                                                       size_t bb,
                                                       lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildBr(lean_to_Builder(builder), lean_to_BasicBlock(bb));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_store(size_t ctx,
    size_t builder, size_t v, size_t slot, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildStore(lean_to_Builder(builder),
                                      lean_to_Value(v), lean_to_Value(slot));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_load2(size_t ctx,
    size_t builder, size_t ty, size_t slot, lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildLoad2(
        lean_to_Builder(builder), lean_to_Type(ty), lean_to_Value(slot), lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_alloca(size_t ctx,
    size_t builder, size_t type, lean_object *name, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildAlloca(
        lean_to_Builder(builder), lean_to_Type(type), lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ret(size_t ctx, size_t builder,
                                                        size_t v,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildRet(lean_to_Builder(builder), lean_to_Value(v));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ret_void(
    size_t builder, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildRetVoid(lean_to_Builder(builder));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_unreachable(size_t ctx,
    size_t builder, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildUnreachable(lean_to_Builder(builder));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_inbounds_gep2(size_t ctx,
    size_t builder, size_t ty, size_t pointer, lean_object *indices, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else

    lean::array_ref<lean_object *> indices_array_ref(indices, true);
    LLVMValueRef *indices_carr = array_ref_to_ArrayLLVMValue(indices_array_ref);
    lean::string_ref name_ref(name, true);

    LLVMValueRef out = LLVMBuildInBoundsGEP2(
        lean_to_Builder(builder), lean_to_Type(ty), lean_to_Value(pointer), indices_carr,
        indices_array_ref.size(), name_ref.data());
    free(indices_carr);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_gep2(size_t ctx, size_t builder,
                                                        size_t ty,
                                                        size_t pointer,
                                                        lean_object *indices,
                                                        lean_object *name,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    lean::array_ref<lean_object *> indices_array_ref(indices, true);
    LLVMValueRef *indices_carr = array_ref_to_ArrayLLVMValue(indices_array_ref);
    lean::string_ref name_ref(name, true);

    LLVMValueRef out =
        LLVMBuildGEP2(lean_to_Builder(builder), lean_to_Type(ty), lean_to_Value(pointer),
                     indices_carr, indices_array_ref.size(), name_ref.data());
    free(indices_carr);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_sext(size_t ctx,
    size_t builder, size_t val, size_t destty, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildSExt(lean_to_Builder(builder), lean_to_Value(val),
                      lean_to_Type(destty), lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_zext(size_t ctx,
    size_t builder, size_t val, size_t destty, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildZExt(lean_to_Builder(builder), lean_to_Value(val),
                      lean_to_Type(destty), lean_string_cstr(name));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_sext_or_trunc(size_t ctx,
    size_t builder, size_t val, size_t destty, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMTypeRef valType = LLVMTypeOf(lean_to_Value(val));
    LLVMValueRef out;
    if (LLVMGetIntTypeWidth(valType) ==
        LLVMGetIntTypeWidth(lean_to_Type(destty))) {
        out = lean_to_Value(val);
    } else if (LLVMGetIntTypeWidth(valType) <
               LLVMGetIntTypeWidth(lean_to_Type(destty))) {
        out = LLVMBuildSExt(lean_to_Builder(builder), lean_to_Value(val),
                            lean_to_Type(destty), lean_string_cstr(name));
    } else {
        out = LLVMBuildTrunc(lean_to_Builder(builder), lean_to_Value(val),
                             lean_to_Type(destty), lean_string_cstr(name));
    }
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_switch(size_t ctx,
    size_t builder, size_t val, size_t elsebb, uint64_t numCases,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildSwitch(lean_to_Builder(builder), lean_to_Value(val),
                        lean_to_BasicBlock(elsebb), numCases);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ptr_to_int(size_t ctx,
    size_t builder, size_t ptr, size_t destty, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildPtrToInt(lean_to_Builder(builder), lean_to_Value(ptr),
                          lean_to_Type(destty), lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_mul(size_t ctx,
        size_t builder,
                                                        size_t lhs, size_t rhs,
                                                        lean_object *name,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildMul(lean_to_Builder(builder), lean_to_Value(lhs),
                     lean_to_Value(rhs), lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_add(size_t ctx, size_t builder,
                                                        size_t lhs, size_t rhs,
                                                        lean_object *name,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildAdd(lean_to_Builder(builder), lean_to_Value(lhs),
                     lean_to_Value(rhs), lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_sub(size_t ctx, size_t builder,
                                                        size_t lhs, size_t rhs,
                                                        lean_object *name,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out =
        LLVMBuildSub(lean_to_Builder(builder), lean_to_Value(lhs),
                     lean_to_Value(rhs), lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_not(size_t ctx, size_t builder,
                                                        size_t v,
                                                        lean_object *name,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildNot(lean_to_Builder(builder), lean_to_Value(v),
                                    lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_icmp(size_t ctx,
    size_t builder, uint64_t predicate, size_t x, size_t y, lean_object *name,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMBuildICmp(
        lean_to_Builder(builder), LLVMIntPredicate(predicate), lean_to_Value(x),
        lean_to_Value(y), lean_string_cstr(name));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_case(size_t ctx, size_t switch_,
                                                       size_t onVal,
                                                       size_t destbb,
                                                       lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMAddCase(lean_to_Value(switch_), lean_to_Value(onVal),
                lean_to_BasicBlock(destbb));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_basic_block_parent(size_t ctx,
    size_t bb, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetBasicBlockParent(lean_to_BasicBlock(bb));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_insert_block(size_t ctx,
    size_t builder, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMBasicBlockRef out = LLVMGetInsertBlock(lean_to_Builder(builder));
    return lean_io_result_mk_ok(lean_box_usize(BasicBlock_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_type_of(size_t ctx, size_t val,
                                                      lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMTypeRef ty = LLVMTypeOf(lean_to_Value(val));
    return lean_io_result_mk_ok(lean_box_usize(Type_to_lean(ty)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_print_module_to_string(size_t ctx,
    size_t mod, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    const char *s = LLVMPrintModuleToString(lean_to_Module(mod));
    return lean_io_result_mk_ok(lean::mk_string(s));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_print_module_to_file(size_t ctx,
    size_t mod, lean_object *file, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    char *err_str = NULL;
    const char *file_cstr = lean_string_cstr(file);
    int is_error = LLVMPrintModuleToFile(lean_to_Module(mod), file_cstr,
                          /*errorMessage=*/&err_str);
    if (is_error) {
        fprintf(stderr, "'%30s' file:%30s ERROR: %30s\n", __FUNCTION__, file_cstr, err_str);
    }

    lean_always_assert(!is_error && "failed to print module to file");
    lean_always_assert (err_str == NULL);
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_int(size_t ctx, size_t ty, uint64_t val,
                                                        uint8_t sext,
                                                        lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMConstInt(lean_to_Type(ty), val, sext);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_array(
    size_t ctx, size_t elemty, lean_object *args, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    lean::array_ref<lean_object *> args_array_ref(args, true);
    LLVMValueRef *args_carr = array_ref_to_ArrayLLVMValue(args_array_ref);
    LLVMValueRef out =
        LLVMConstArray(lean_to_Type(elemty), args_carr, args_array_ref.size());
    free(args_carr);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_string(
    size_t ctx, lean_object *s, lean_object * /* w */) {
    lean::string_ref sref = lean::string_ref(s, true);
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else

    LLVMValueRef out =
        LLVMConstStringInContext(lean_to_Context(ctx), sref.data(),
                                 sref.length(), /*DontNullTerminate=*/false);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_pointer_null(
    size_t ctx, size_t elemty, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else

    LLVMValueRef out = LLVMConstPointerNull(lean_to_Type(elemty));

    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *llvm_get_param(size_t ctx, size_t f, uint64_t ix,
                                                   lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetParam(lean_to_Value(f), ix);
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object * llvm_count_params(size_t ctx, size_t f,
                                                       lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    unsigned n = LLVMCountParams(lean_to_Value(f));
    return lean_io_result_mk_ok(lean_box_uint64(n));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_set_tail_call(
    size_t ctx, size_t fnval, uint8_t isTail, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMSetTailCall(lean_to_Value(fnval), isTail);
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_memory_buffer_with_contents_of_file(size_t ctx, lean_object *path,
                                                     lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMMemoryBufferRef membuf;
    char *err_str = NULL;
    const char *path_cstr = lean_string_cstr(path);
    int is_error = LLVMCreateMemoryBufferWithContentsOfFile(
        path_cstr, &membuf, &err_str);

    if (is_error) {
        fprintf(stderr, "%20s file:%30s ERROR: %30s\n", __FUNCTION__, path_cstr, err_str);
    }
    lean_always_assert((is_error != 1) && "failed to create membuf from file");
    lean_always_assert(err_str == NULL);
    return lean_io_result_mk_ok(lean_box_usize(MemoryBuffer_to_lean(membuf)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_parse_bitcode(
    size_t context, size_t membuf, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMModuleRef out_module;
    char *err_str = NULL;
    int is_error = LLVMParseBitcodeInContext(lean_to_Context(context),
                                             lean_to_MemoryBuffer(membuf),
                                             &out_module, &err_str);

    if (is_error) {
        fprintf(stderr, "%20s ERROR: %30s\n", __FUNCTION__, err_str);
    }
    lean_always_assert(!is_error && "failed to parse bitcode");
    lean_always_assert(err_str == NULL);
    return lean_io_result_mk_ok(lean_box_usize(Module_to_lean(out_module)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_link_modules(size_t ctx,
    size_t dest_module, size_t src_module, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    int is_error = LLVMLinkModules2(lean_to_Module(dest_module),
                                    lean_to_Module(src_module));

    if (is_error) {
        fprintf(stderr, "%20s ERROR: unable to link modules\n", __FUNCTION__);
    }
    lean_always_assert(!is_error && "failed to link modules");
    return lean_io_result_mk_ok(lean_box(0));
#endif
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_target_machine(size_t ctx,
    size_t target, lean_object *tripleStr, lean_object *cpuStr,
    lean_object *featuresStr, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    // TODO (bollu): expose this option
    const LLVMCodeGenOptLevel optLevel = LLVMCodeGenLevelAggressive;
    const LLVMRelocMode relocMode = LLVMRelocPIC;
    const LLVMCodeModel codeModel = LLVMCodeModelDefault;
    LLVMTargetMachineRef tm = LLVMCreateTargetMachine(
        lean_to_Target(target), lean_string_cstr(tripleStr),
        lean_string_cstr(cpuStr), lean_string_cstr(featuresStr), optLevel,
        relocMode, codeModel);


    return lean_io_result_mk_ok(lean_box_usize(TargetMachine_to_lean(tm)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_target_from_triple(size_t ctx,
    lean_object *triple, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMTargetRef t;
    char *errmsg = NULL;
    int is_error =
        LLVMGetTargetFromTriple(lean_string_cstr(triple), &t, &errmsg);
    if (is_error) {
        fprintf(stderr, "Unable to find target '%s'. Registered targets:\n", lean_string_cstr(triple));
        for(LLVMTargetRef t = LLVMGetFirstTarget();  t != NULL; t = LLVMGetNextTarget(t)) {
            fprintf(stderr, "    %-10s - %s\n", LLVMGetTargetName(t), LLVMGetTargetDescription(t));
        }
    }

    lean_always_assert(!is_error && "failed to get target from triple");
    return lean_io_result_mk_ok(lean_box_usize(Target_to_lean(t)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_default_target_triple(lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    char *triple = LLVMGetDefaultTargetTriple();
    lean_object *out = lean::mk_string(triple);
    free(triple);
    return lean_io_result_mk_ok(out);
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_target_machine_emit_to_file(size_t ctx,
    size_t target_machine, size_t module, lean_object *filepath,
    uint64_t codegenType, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    // TODO (bollu): figure out a story for cross-compilation.
    // We currently choose not to invoke LLVMInitializeAllTargetInfos() etc.
    // since our build system only enables certain backends.
    // LLVMInitializeNativeTargetInfo();

    char *err_msg = NULL;
    char *filepath_c_str = const_cast<char *>(lean_string_cstr(filepath));
    int is_error = LLVMTargetMachineEmitToFile(
        lean_to_TargetMachine(target_machine), lean_to_Module(module),
        filepath_c_str, LLVMCodeGenFileType(codegenType), &err_msg);

    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_pass_manager(size_t ctx,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(PassManager_to_lean(LLVMCreatePassManager())));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_run_pass_manager(size_t ctx, size_t pm, size_t mod,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    int is_error = LLVMRunPassManager(lean_to_PassManager(pm), lean_to_Module(mod));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_dispose_pass_manager(size_t ctx, size_t pm,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMDisposePassManager(lean_to_PassManager(pm));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_pass_manager_builder(size_t ctx,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    return lean_io_result_mk_ok(lean_box_usize(PassManagerBuilder_to_lean(LLVMPassManagerBuilderCreate())));
#endif  // LEAN_LLVM
}


extern "C" LEAN_EXPORT lean_object *lean_llvm_dispose_pass_manager_builder(size_t ctx, size_t pmb,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMPassManagerBuilderDispose(lean_to_PassManagerBuilder(pmb));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}


extern "C" LEAN_EXPORT lean_object *lean_llvm_pass_manager_builder_set_opt_level(size_t ctx, size_t pmb, unsigned opt_level,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMPassManagerBuilderSetOptLevel(lean_to_PassManagerBuilder(pmb), opt_level);
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}


extern "C" LEAN_EXPORT lean_object *lean_llvm_pass_manager_builder_populate_module_pass_manager(size_t ctx, size_t pmb, size_t pm,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMPassManagerBuilderPopulateModulePassManager(lean_to_PassManagerBuilder(pmb), lean_to_PassManager(pm));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_dispose_target_machine(size_t ctx, size_t tm,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMDisposeTargetMachine(lean_to_TargetMachine(tm));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_dispose_module(size_t ctx, size_t mod,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMDisposeModule(lean_to_Module(mod));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_set_visibility(size_t ctx, size_t value, uint64_t vis,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMSetVisibility(lean_to_Value(value), LLVMVisibility(vis));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_set_dll_storage_class(size_t ctx, size_t value, uint64_t cls,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMSetDLLStorageClass(lean_to_Value(value), LLVMDLLStorageClass(cls));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_create_string_attribute(size_t ctx, lean_object* key, lean_object* value,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMAttributeRef attr = LLVMCreateStringAttribute(lean_to_Context(ctx), lean_string_cstr(key), lean_string_len(key), lean_string_cstr(value), lean_string_len(value));
    return lean_io_result_mk_ok(lean_box_usize(Attribute_to_lean(attr)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_add_attribute_at_index(size_t ctx, size_t fn, uint64_t idx, size_t attr,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMAddAttributeAtIndex(lean_to_Value(fn), idx, lean_to_Attribute(attr));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_first_global(size_t ctx, size_t mod,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetFirstGlobal(lean_to_Module(mod));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_next_global(size_t ctx, size_t global,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetNextGlobal(lean_to_Value(global));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_first_function(size_t ctx, size_t mod,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetFirstFunction(lean_to_Module(mod));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_next_function(size_t ctx, size_t function,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMValueRef out = LLVMGetNextFunction(lean_to_Value(function));
    return lean_io_result_mk_ok(lean_box_usize(Value_to_lean(out)));
#endif  // LEAN_LLVM
}


extern "C" LEAN_EXPORT lean_object *lean_llvm_set_linkage(size_t ctx, size_t value, uint64_t linkage,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    LLVMSetLinkage(lean_to_Value(value), LLVMLinkage(linkage));
    return lean_io_result_mk_ok(lean_box(0));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_get_value_name2(size_t ctx, size_t value,
    lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
    size_t len;
    const char *name = LLVMGetValueName2(lean_to_Value(value), &len);
    return lean_io_result_mk_ok(lean::mk_string(name));
#endif  // LEAN_LLVM
}

extern "C" LEAN_EXPORT lean_object *llvm_is_declaration(size_t ctx, size_t global, lean_object * /* w */) {
#ifndef LEAN_LLVM
    lean_always_assert(
        false && ("Please build a version of Lean4 with -DLLVM=ON to invoke "
                  "the LLVM backend function."));
#else
	uint8_t is_bool = LLVMIsDeclaration(lean_to_Value(global));
	return lean_io_result_mk_ok(lean_box(is_bool));
#endif  // LEAN_LLVM
}
