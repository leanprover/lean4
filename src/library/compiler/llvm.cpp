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
#include <llvm-c/BitReader.h>
#include <llvm-c/Core.h>
#include <llvm-c/Types.h>
#include <llvm-c/Linker.h>
#include <llvm-c/Target.h>
#include <llvm-c/TargetMachine.h>

#include "runtime/array_ref.h"
#include "runtime/string_ref.h"

#define LLVM_DEBUG 0

static void donothing_finalize(void *obj) {
  (void)obj;
  // delete static_cast<S*>(obj);
}

static void donothing_foreach(void *, b_lean_obj_arg) {
  // do nothing since `S` does not contain nested Lean objects
}

// == LLVM <-> Lean: Target ==

static lean_external_class *g_Target_class = nullptr;

static inline lean_object *Target_to_lean(LLVMTargetRef s) {
  if (g_Target_class == nullptr) {
    g_Target_class =
        lean_register_external_class(donothing_finalize, donothing_foreach);
  }
  return lean_alloc_external(g_Target_class, s);
}

static inline LLVMTargetRef lean_to_Target(b_lean_obj_arg s) {
  return static_cast<LLVMTargetRef>(lean_get_external_data(s));
}


// == LLVM <-> Lean: TargetMachine ==

static lean_external_class *g_TargetMachine_class = nullptr;

static inline lean_object *TargetMachine_to_lean(LLVMTargetMachineRef s) {
  if (g_TargetMachine_class == nullptr) {
    g_TargetMachine_class =
        lean_register_external_class(donothing_finalize, donothing_foreach);
  }
  return lean_alloc_external(g_TargetMachine_class, s);
}

static inline LLVMTargetMachineRef lean_to_TargetMachine(b_lean_obj_arg s) {
  return static_cast<LLVMTargetMachineRef>(lean_get_external_data(s));
}


// == LLVM <-> Lean: MemoryBuffer ==

static lean_external_class *g_MemoryBuffer_class = nullptr;

static inline lean_object *MemoryBuffer_to_lean(LLVMMemoryBufferRef s) {
  if (g_MemoryBuffer_class == nullptr) {
    g_MemoryBuffer_class =
        lean_register_external_class(donothing_finalize, donothing_foreach);
  }
  return lean_alloc_external(g_MemoryBuffer_class, s);
}

static inline LLVMMemoryBufferRef lean_to_MemoryBuffer(b_lean_obj_arg s) {
  return static_cast<LLVMMemoryBufferRef>(lean_get_external_data(s));
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
LLVMTypeRef *
array_ref_to_ArrayLLVMType(const lean::array_ref<lean_object *> &arr) {
  const int nargs = arr.size(); // lean::array_size(args);
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
LLVMValueRef *
array_ref_to_ArrayLLVMValue(const lean::array_ref<lean_object *> &arr) {
  const int nargs = arr.size(); // lean::array_size(args);
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

extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_context(lean_object * /* w */) {
  LLVMContextRef ctx = LLVMContextCreate();
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
  }
  return lean_io_result_mk_ok(Context_to_lean(ctx));
};

// opaque createModule (ctx: @&Ptr Context) (name: @&String): IO (Ptr Module)
extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_module(lean_object *ctx, lean_object *str,
                        lean_object * /* w */) {
  LLVMModuleRef mod =
     LLVMModuleCreateWithNameInContext(lean_string_cstr(str), lean_to_Context(ctx));
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
  }
  // LLVMWriteBitcodeToFile(mod, "/home/bollu/temp/module.bc");
  return lean_io_result_mk_ok(Module_to_lean(mod));
};

extern "C" LEAN_EXPORT lean_object *
lean_llvm_write_bitcode_to_file(lean_object *mod, lean_object *filepath,
                                lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
  }
  const int err =
      LLVMWriteBitcodeToFile(lean_to_Module(mod), lean_string_cstr(filepath));
  assert(!err && "unable to write bitcode");
  return lean_io_result_mk_ok(lean_box(0)); // IO Unit
};

extern "C" LEAN_EXPORT lean_object *
lean_llvm_module_to_string(lean_object *mod, lean_object * /* w */) {
  // return lean_io_result_mk_ok(lean_mk_string(g_s.m_s.c_str()));
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
  }
  return lean_io_result_mk_ok(lean_mk_string(LLVMPrintModuleToString(lean_to_Module(mod))));
};

extern "C" LEAN_EXPORT lean_object *
lean_llvm_add_function(lean_object *mod, lean_object *name, lean_object *type,
                       lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; lean_llvm_add_function: %p\n", __PRETTY_FUNCTION__,
            mod);
  }
  if (LLVM_DEBUG) {
    fprintf(stderr, "... %s ; name: %s \n", __PRETTY_FUNCTION__,
            lean_string_cstr(name));
  }
  if (LLVM_DEBUG) {
    fprintf(stderr, "... %s ; type: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(type)));
  }
  LLVMValueRef out =
    LLVMAddFunction(
      lean_to_Module(mod), lean_string_cstr(name), lean_to_Type(type));
  if (LLVM_DEBUG) {
    fprintf(stderr, "... %s ; out: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_named_function(lean_object *mod, lean_object *name,
                             lean_object * /* w */) {
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

extern "C" LEAN_EXPORT lean_object *
lean_llvm_add_global(lean_object *mod, lean_object *name, lean_object *type,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; mod: %p\n", __PRETTY_FUNCTION__, mod);
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
    fprintf(stderr, "...%s ; type: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(type)));
  }
  LLVMValueRef out = LLVMAddGlobal(lean_to_Module(mod), lean_to_Type(type), lean_string_cstr(name));
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  }
  
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_named_global(lean_object *mod, lean_object *name,
                           lean_object * /* w */) {
  LLVMValueRef g =
      LLVMGetNamedGlobal(lean_to_Module(mod), lean_string_cstr(name));
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
    fprintf(stderr, "...%s ; g: %p\n", __PRETTY_FUNCTION__, g);
  }
  return lean_io_result_mk_ok(g ? lean::mk_option_some(Value_to_lean(g))
                                : lean::mk_option_none());
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_global_string(lean_object *builder, lean_object *str, lean_object *name, lean_object * /* w */) {
  lean::string_ref sref = lean::string_ref(str, true);
  lean::string_ref nameref = lean::string_ref(name, true);
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; s: %s\n", __PRETTY_FUNCTION__, sref.data());
    fprintf(stderr, "...%s ; s: %s\n", __PRETTY_FUNCTION__, nameref.data());
  }

  LLVMValueRef out = LLVMBuildGlobalString(lean_to_Builder(builder), 
					   sref.data(), nameref.data());
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}
extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_undef(lean_object *ty,
                           lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(ty)));
  }
  LLVMValueRef out = LLVMGetUndef(lean_to_Type(ty));
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}



extern "C" LEAN_EXPORT lean_object *
lean_llvm_set_initializer(lean_object *global, lean_object *initializer,
                          lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; global: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(global)));
    fprintf(stderr, "...%s ; initializer: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(initializer)));
  }
  LLVMSetInitializer(lean_to_Value(global), lean_to_Value(initializer));
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_function_type(lean_object *retty, lean_object *argtys,
                        uint8_t isvararg, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; retty: %p\n", __PRETTY_FUNCTION__, retty);
    fprintf(stderr, "... %s ; retty: %s \n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(retty)));
  }
  lean::array_ref<lean_object *> arr(
      argtys, true); // TODO: why do I need to bump up refcount here?
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

extern "C" LEAN_EXPORT lean_object *
lean_llvm_int_type_in_context(lean_object *ctx, uint64_t width,
                              lean_object * /* w */) {
  // bollu, TODO: Check that this actually works.
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; %lu \n", __PRETTY_FUNCTION__, width);
  }
  return lean_io_result_mk_ok(
      Type_to_lean(LLVMIntTypeInContext(lean_to_Context(ctx), width)));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_float_type_in_context(lean_object *ctx, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
  }
  return lean_io_result_mk_ok(
      Type_to_lean(LLVMFloatTypeInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_void_type_in_context(lean_object *ctx, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
  }
  return lean_io_result_mk_ok(
      Type_to_lean(LLVMVoidTypeInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_double_type_in_context(lean_object *ctx, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; \n", __PRETTY_FUNCTION__);
  }
  return lean_io_result_mk_ok(
      Type_to_lean(LLVMDoubleTypeInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_pointer_type(lean_object *base, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; base: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(base)));
  }
  LLVMTypeRef out = LLVMPointerType(lean_to_Type(base), /*addrspace=*/0);
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintTypeToString(out));
  return lean_io_result_mk_ok(Type_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_array_type(lean_object *base, uint64_t nelem, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; base: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(base)));
    fprintf(stderr, "...%s ; nelem: %lu", __PRETTY_FUNCTION__, nelem);
  }
  LLVMTypeRef out = LLVMArrayType(lean_to_Type(base), /*nelem=*/nelem);
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintTypeToString(out));
  return lean_io_result_mk_ok(Type_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_builder_in_context(lean_object *ctx, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
  }
  return lean_io_result_mk_ok(
      Builder_to_lean(LLVMCreateBuilderInContext(lean_to_Context(ctx))));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_append_basic_block_in_context(lean_object *ctx, lean_object *fn,
                                        lean_object *name,
                                        lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ctx: %p\n", __PRETTY_FUNCTION__, ctx);
    fprintf(stderr, "...%s ; fn: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(fn)));
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__,
            lean_string_cstr(name));
  }
  LLVMBasicBlockRef bb = LLVMAppendBasicBlockInContext(
      lean_to_Context(ctx), lean_to_Value(fn), lean_string_cstr(name));
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
  }
  return lean_io_result_mk_ok(BasicBlock_to_lean(bb));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_position_builder_at_end(lean_object *builder, lean_object *bb,
                                  lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, ".....%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
    fprintf(stderr, ".....%s ; fn: %s\n", __PRETTY_FUNCTION__,
	    LLVMPrintValueToString(LLVMGetBasicBlockParent(lean_to_BasicBlock(bb))));
  }
  LLVMPositionBuilderAtEnd(lean_to_Builder(builder), lean_to_BasicBlock(bb));
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_clear_insertion_position(lean_object *builder,
                                   lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
  }
  LLVMClearInsertionPosition(lean_to_Builder(builder));
  return lean_io_result_mk_ok(lean_box(0));
}


extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_call2(lean_object *builder, lean_object *fnty,
                      lean_object *fnval, lean_object *args, lean_object *name,
                      lean_object * /* w */) {
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
      args, true); // TODO: why do I need to bump up refcount here?
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

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_call(lean_object *builder, lean_object *fnval,
                     lean_object *args, lean_object *name,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; fnval: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(fnval)));
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__,
            lean_string_cstr(name));
  }
  lean::array_ref<lean_object *> arr(
      args, true); // TODO: why do I need to bump up refcount here?
  if (LLVM_DEBUG) {
    fprintf(stderr, "... %s ; arr.size(): %zu\n", __PRETTY_FUNCTION__,
            arr.size());
  }
  LLVMValueRef *arrArgVals = array_ref_to_ArrayLLVMValue(arr);
  LLVMValueRef out =
      LLVMBuildCall(lean_to_Builder(builder), lean_to_Value(fnval), arrArgVals,
                    arr.size(), lean_string_cstr(name));
  free(arrArgVals);
  if (LLVM_DEBUG) {
    fprintf(stderr, "... %s ; out: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_cond_br(lean_object *builder, lean_object *if_,
                        lean_object *thenbb, lean_object *elsebb,
                        lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; if_: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(if_)));
    fprintf(stderr, "...%s ; thenbb: %p\n", __PRETTY_FUNCTION__, thenbb);
    fprintf(stderr, "...%s ; elsebb: %p\n", __PRETTY_FUNCTION__, elsebb);
  }
  LLVMValueRef out =
      LLVMBuildCondBr(lean_to_Builder(builder), lean_to_Value(if_),
                      lean_to_BasicBlock(thenbb), lean_to_BasicBlock(elsebb));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_br(lean_object *builder,
                                                       lean_object *bb,
                                                       lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
  }
  LLVMValueRef out =
      LLVMBuildBr(lean_to_Builder(builder), lean_to_BasicBlock(bb));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_store(lean_object *builder, lean_object *v, lean_object *slot,
                      lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; v: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(v)));
    fprintf(stderr, "...%s ; slot: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(slot)));
  }
  LLVMValueRef out = LLVMBuildStore(lean_to_Builder(builder), lean_to_Value(v),
                                    lean_to_Value(slot));
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_load(lean_object *builder, lean_object *slot, lean_object *name,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; slot: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(slot)));
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__,
            lean_string_cstr(name));
  }
  LLVMValueRef out = LLVMBuildLoad(lean_to_Builder(builder),
                                   lean_to_Value(slot), lean_string_cstr(name));
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_alloca(lean_object *builder, lean_object *type,
                       lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; ty: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(type)));
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__,
            lean_string_cstr(name));
  }
  LLVMValueRef out = LLVMBuildAlloca(
      lean_to_Builder(builder), lean_to_Type(type), lean_string_cstr(name));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_build_ret(lean_object *builder,
                                                        lean_object *v,
                                                        lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; v: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(v)));
  }
  LLVMValueRef out = LLVMBuildRet(lean_to_Builder(builder), lean_to_Value(v));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_ret_void(lean_object *builder, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
  }
  LLVMValueRef out = LLVMBuildRetVoid(lean_to_Builder(builder));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_unreachable(lean_object *builder, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
  }
  LLVMValueRef out = LLVMBuildUnreachable(lean_to_Builder(builder));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_inbounds_gep(lean_object *builder, lean_object *pointer, lean_object *indices,
			     lean_object *name, lean_object * /* w */) {
  lean::array_ref<lean_object *> indices_array_ref(
      indices, true); // TODO: why do I need to bump up refcount here?
  LLVMValueRef *indices_carr = array_ref_to_ArrayLLVMValue(indices_array_ref);
  lean::string_ref name_ref(name, true);
  
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; pointer: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(pointer)));
  }
  LLVMValueRef out = LLVMBuildInBoundsGEP(lean_to_Builder(builder), lean_to_Value(pointer),
					  indices_carr, indices_array_ref.size(), name_ref.data());
  free(indices_carr);
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_gep(lean_object *builder, lean_object *pointer, lean_object *indices,
			     lean_object *name, lean_object * /* w */) {
  lean::array_ref<lean_object *> indices_array_ref(
      indices, true); // TODO: why do I need to bump up refcount here?
  LLVMValueRef *indices_carr = array_ref_to_ArrayLLVMValue(indices_array_ref);
  lean::string_ref name_ref(name, true);
  
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; pointer: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(pointer)));
  }
  LLVMValueRef out = LLVMBuildGEP(lean_to_Builder(builder), lean_to_Value(pointer),
					  indices_carr, indices_array_ref.size(), name_ref.data());
  free(indices_carr);
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}


extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_pointer_cast(lean_object *builder, lean_object *val, lean_object *destty,
			     lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    fprintf(stderr, "...%s ; destty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(destty)));    
  }
  LLVMValueRef out = LLVMBuildPointerCast(lean_to_Builder(builder), lean_to_Value(val), lean_to_Type(destty),
					 lean_string_cstr(name));
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_sext(lean_object *builder, lean_object *val, lean_object *destty,
			     lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    fprintf(stderr, "...%s ; destty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(destty)));    
  }
  LLVMValueRef out = LLVMBuildSExt(lean_to_Builder(builder), lean_to_Value(val), lean_to_Type(destty),
					 lean_string_cstr(name));
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_zext(lean_object *builder, lean_object *val, lean_object *destty,
			     lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    fprintf(stderr, "...%s ; destty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(destty)));    
  }
  LLVMValueRef out = LLVMBuildZExt(lean_to_Builder(builder), lean_to_Value(val), lean_to_Type(destty),
					 lean_string_cstr(name));
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_sext_or_trunc(lean_object *builder, lean_object *val, lean_object *destty,
			     lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    fprintf(stderr, "...%s ; destty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(destty)));    
  }
  LLVMTypeRef valType = LLVMTypeOf(lean_to_Value(val));
  LLVMValueRef out;
  if (LLVMGetIntTypeWidth(valType) == LLVMGetIntTypeWidth(lean_to_Type(destty))) {
    out = lean_to_Value(val);
  } else if (LLVMGetIntTypeWidth(valType) < LLVMGetIntTypeWidth(lean_to_Type(destty))) {
    out = LLVMBuildSExt(lean_to_Builder(builder), lean_to_Value(val), lean_to_Type(destty),
				   lean_string_cstr(name));
  } else {
    out = LLVMBuildTrunc(lean_to_Builder(builder), lean_to_Value(val), lean_to_Type(destty),
				   lean_string_cstr(name));
  }
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}


extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_switch(lean_object *builder, lean_object *val, lean_object *elsebb,
			     uint64_t numCases, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(val)));
    fprintf(stderr, "...%s ; elsebb: %p\n", __PRETTY_FUNCTION__, elsebb);
    fprintf(stderr, "...%s ; numCases: %lu\n", __PRETTY_FUNCTION__, numCases);    
  }
  LLVMValueRef out = LLVMBuildSwitch(lean_to_Builder(builder), lean_to_Value(val), lean_to_BasicBlock(elsebb),
				     numCases);
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_ptr_to_int(lean_object *builder, lean_object *ptr, lean_object *destty, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; ptr: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(ptr)));
  }
  LLVMValueRef out = LLVMBuildPtrToInt(lean_to_Builder(builder), lean_to_Value(ptr),
				       lean_to_Type(destty), lean_string_cstr(name));

  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_mul(lean_object *builder, lean_object *lhs, lean_object *rhs, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; lhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(lhs)));
    fprintf(stderr, "...%s ; rhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(rhs)));
  }
  LLVMValueRef out = LLVMBuildMul(lean_to_Builder(builder), lean_to_Value(lhs), lean_to_Value(rhs), 
				       lean_string_cstr(name));
  
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_add(lean_object *builder, lean_object *lhs, lean_object *rhs, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; lhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(lhs)));
    fprintf(stderr, "...%s ; rhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(rhs)));
  }
  LLVMValueRef out = LLVMBuildAdd(lean_to_Builder(builder), lean_to_Value(lhs), lean_to_Value(rhs), 
				       lean_string_cstr(name));
  
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_sub(lean_object *builder, lean_object *lhs, lean_object *rhs, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; lhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(lhs)));
    fprintf(stderr, "...%s ; rhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(rhs)));
  }
  LLVMValueRef out = LLVMBuildSub(lean_to_Builder(builder), lean_to_Value(lhs), lean_to_Value(rhs), 
				       lean_string_cstr(name));
  
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_not(lean_object *builder, lean_object *v, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; lhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(v)));
  }
  LLVMValueRef out = LLVMBuildNot(lean_to_Builder(builder), lean_to_Value(v),
				       lean_string_cstr(name));
  
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_build_icmp(lean_object *builder, uint64_t predicate, lean_object *x, lean_object *y, lean_object *name, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; : %p\n", __PRETTY_FUNCTION__, builder);
    fprintf(stderr, "...%s ; predicate: %lu\n", __PRETTY_FUNCTION__, predicate);
    fprintf(stderr, "...%s ; lhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(x)));
    fprintf(stderr, "...%s ; rhs: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(y)));
    fprintf(stderr, "...%s ; name: %s\n", __PRETTY_FUNCTION__, lean_string_cstr(name));
  }
  LLVMValueRef out = LLVMBuildICmp(lean_to_Builder(builder),
				   LLVMIntPredicate(predicate),
				   lean_to_Value(x),
				   lean_to_Value(y),
				   lean_string_cstr(name));
  
  fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}




extern "C" LEAN_EXPORT lean_object *
lean_llvm_add_case (lean_object *switch_, lean_object *onVal, lean_object *destbb, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ;\n", __PRETTY_FUNCTION__);
    fprintf(stderr, "...%s ; switch_: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(switch_)));
    fprintf(stderr, "...%s ; onVal: %s\n", __PRETTY_FUNCTION__, LLVMPrintValueToString(lean_to_Value(onVal)));
    fprintf(stderr, "...%s ; destbb: %p\n", __PRETTY_FUNCTION__, destbb);    
  }
  LLVMAddCase(lean_to_Value(switch_),
	      lean_to_Value(onVal),
	      lean_to_BasicBlock(destbb));
  return lean_io_result_mk_ok(lean_box(0));


}


extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_basic_block_parent(lean_object *bb, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; bb: %p\n", __PRETTY_FUNCTION__, bb);
  }
  LLVMValueRef out = LLVMGetBasicBlockParent(lean_to_BasicBlock(bb));
  fprintf(stderr, "...%s ; parent: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_insert_block(lean_object *builder, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; builder: %p\n", __PRETTY_FUNCTION__, builder);
  }
  LLVMBasicBlockRef out = LLVMGetInsertBlock(lean_to_Builder(builder));
  return lean_io_result_mk_ok(BasicBlock_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_type_of(lean_object *val,
                                                      lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; val: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(val)));
  }
  LLVMTypeRef ty = LLVMTypeOf(lean_to_Value(val));
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; ty: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(ty));
  }
  return lean_io_result_mk_ok(Type_to_lean(ty));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_print_module_to_string(lean_object *mod, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; module: %p\n", __PRETTY_FUNCTION__, mod);
  }
  const char *s = LLVMPrintModuleToString(lean_to_Module(mod));
  return lean_io_result_mk_ok(lean::mk_string(s));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_print_module_to_file(lean_object *mod, lean_object *file,
                               lean_object * /* w */) {
  LLVMPrintModuleToFile(lean_to_Module(mod), lean_string_cstr(file),
                        /*errorMessage=*/NULL);
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *lean_llvm_const_int(lean_object *ty,
                                                        uint64_t val,
                                                        uint8_t sext,
                                                        lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ty: %p\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(ty)));
    fprintf(stderr, "...%s ; val: %lu\n", __PRETTY_FUNCTION__, val);
    fprintf(stderr, "...%s ; sext: %d\n", __PRETTY_FUNCTION__, (int)sext);
  }
  LLVMValueRef out = LLVMConstInt(lean_to_Type(ty), val, sext);
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_const_array(lean_object *elemty, lean_object *args,
                      lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; ty: %p\n", __PRETTY_FUNCTION__,
            LLVMPrintTypeToString(lean_to_Type(elemty)));
  }
  lean::array_ref<lean_object *> args_array_ref(
      args, true); // TODO: why do I need to bump up refcount here?
  LLVMValueRef *args_carr = array_ref_to_ArrayLLVMValue(args_array_ref);
  LLVMValueRef out =
      LLVMConstArray(lean_to_Type(elemty), args_carr, args_array_ref.size());
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  free(args_carr);
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_const_string(lean_object *ctx, lean_object *s, lean_object * /* w */) {
  lean::string_ref sref = lean::string_ref(s, true);
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; s: %s\n", __PRETTY_FUNCTION__, sref.data());
  }

  LLVMValueRef out = LLVMConstStringInContext(lean_to_Context(ctx),
					      sref.data(),
					      sref.length(), /*DontNullTerminate=*/false);
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; val: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_const_pointer_null(lean_object *elemty, lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; elemty: %s\n", __PRETTY_FUNCTION__, LLVMPrintTypeToString(lean_to_Type(elemty)));
  }

  LLVMValueRef out = LLVMConstPointerNull(lean_to_Type(elemty));

  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; out: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(out));
  }
  return lean_io_result_mk_ok(Value_to_lean(out));
}


extern "C" LEAN_EXPORT lean_object *llvm_get_param(lean_object *f, uint64_t ix,
                                                   lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; f: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(f)));
    fprintf(stderr, "...%s ; ix: %lu\n", __PRETTY_FUNCTION__, ix);
  }
  LLVMValueRef out = LLVMGetParam(lean_to_Value(f), ix);
  fprintf(stderr, "%s ; out: %s\n", __PRETTY_FUNCTION__,
          LLVMPrintValueToString(out));
  return lean_io_result_mk_ok(Value_to_lean(out));
}

extern "C" LEAN_EXPORT uint64_t llvm_count_params(lean_object *f,
                                                  lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; f: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(f)));
  }
  int n = LLVMCountParams(lean_to_Value(f));
  fprintf(stderr, "%s ; n: %d\n", __PRETTY_FUNCTION__, n);
  return n;
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_set_tail_call(lean_object *fnval, uint8_t isTail,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; fnval: %s\n", __PRETTY_FUNCTION__,
            LLVMPrintValueToString(lean_to_Value(fnval)));
    fprintf(stderr, "...%s ; isTail?: %d\n", __PRETTY_FUNCTION__,
            isTail);
  }
  LLVMSetTailCall(lean_to_Value(fnval), isTail);
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_memory_buffer_with_contents_of_file(lean_object *path,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; path: %s \n", __PRETTY_FUNCTION__,
	    lean_string_cstr(path));
  }
  LLVMMemoryBufferRef membuf;
  char *err_str = NULL;
  int is_error = LLVMCreateMemoryBufferWithContentsOfFile(lean_string_cstr(path), &membuf, &err_str);
    if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; error?: %d \n", __PRETTY_FUNCTION__, is_error);
  }

  assert((is_error != 1)&& "failed to link modules");
  return lean_io_result_mk_ok(MemoryBuffer_to_lean(membuf));
}


extern "C" LEAN_EXPORT lean_object *
lean_llvm_parse_bitcode(lean_object *context, lean_object *membuf,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; membuf: %p \n", __PRETTY_FUNCTION__,
	    membuf);
  }
  LLVMModuleRef out_module;
  char *err_str = NULL;
  int is_error = LLVMParseBitcodeInContext(lean_to_Context(context),
					   lean_to_MemoryBuffer(membuf),
					   &out_module, &err_str);
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; error?: %d \n", __PRETTY_FUNCTION__, is_error);
  }

  assert(!is_error && "failed to link modules");
  return lean_io_result_mk_ok(Module_to_lean(out_module));
}



extern "C" LEAN_EXPORT lean_object *
lean_llvm_link_modules(lean_object *dest_module, lean_object *src_module,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; dest_module: %p \n", __PRETTY_FUNCTION__,
	    dest_module);
    fprintf(stderr, "...%s ; src_module: %p\n", __PRETTY_FUNCTION__,
	    src_module);
  }
  int is_error = LLVMLinkModules2(lean_to_Module(dest_module), lean_to_Module(src_module));
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; error?: %d \n", __PRETTY_FUNCTION__, is_error);
  }

  assert(!is_error && "failed to link modules");
  return lean_io_result_mk_ok(lean_box(0));
}

// opaque createTargetMachine (target: @&Ptr Target) (tripleStr: @&String) (cpu: @&String) (features: @&String): IO (Ptr TargetMachine)
extern "C" LEAN_EXPORT lean_object *
lean_llvm_create_target_machine(lean_object *target, lean_object *tripleStr,
				lean_object *cpuStr, lean_object *featuresStr,
                     lean_object * /* w */) {
  if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; target: %p \n", __PRETTY_FUNCTION__,
	    lean_to_Target(target));
    fprintf(stderr, "...%s ; tripleStr: %p\n", __PRETTY_FUNCTION__,
	    lean_string_cstr(tripleStr));
    fprintf(stderr, "...%s ; cpuStr: %p\n", __PRETTY_FUNCTION__,
	    lean_string_cstr(cpuStr));
    fprintf(stderr, "...%s ; featuresStr: %p\n", __PRETTY_FUNCTION__,
	    lean_string_cstr(featuresStr));
  }
  // TODO (bollu): expose this option
  const LLVMCodeGenOptLevel optLevel = LLVMCodeGenLevelAggressive;
  const LLVMRelocMode relocMode = LLVMRelocPIC;
  const LLVMCodeModel codeModel = LLVMCodeModelDefault;
  LLVMTargetMachineRef tm =
    LLVMCreateTargetMachine(lean_to_Target(target),
			  lean_string_cstr(tripleStr),
			  lean_string_cstr(cpuStr),
			  lean_string_cstr(featuresStr),
			  optLevel,
			  relocMode,
			    codeModel);
  
  if (LLVM_DEBUG) {
    fprintf(stderr, "...%s ; out: %p \n", __PRETTY_FUNCTION__, tm);
  }

  return lean_io_result_mk_ok(TargetMachine_to_lean(tm));
}

// opaque getTargetFromTriple (triple: @&String): IO (Ptr Target)
extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_target_from_triple(lean_object *triple,
                     lean_object * /* w */) {
    if (LLVM_DEBUG) {
    fprintf(stderr, "%s ; triple: %p \n", __PRETTY_FUNCTION__,
	    lean_string_cstr(triple));
    }
    LLVMTargetRef t;
    char *errmsg = NULL;
    int is_error = LLVMGetTargetFromTriple(lean_string_cstr(triple), &t, &errmsg);
    assert(!is_error && "failed to get target from triple");
    if (LLVM_DEBUG) {
      fprintf(stderr, "...%s ; error?: %d \n", __PRETTY_FUNCTION__, is_error);
      fprintf(stderr, "...%p ; t: %p \n", __PRETTY_FUNCTION__, t);
    }
    return lean_io_result_mk_ok(Target_to_lean(t));
}

// opaque getDefaultTargetTriple: IO String
extern "C" LEAN_EXPORT lean_object *
lean_llvm_get_default_target_triple(lean_object* /* w */) {
  char *triple = LLVMGetDefaultTargetTriple();
    if (LLVM_DEBUG) {
      fprintf(stderr, "%s; triple: %s \n", __PRETTY_FUNCTION__, triple);
    }
    return lean_io_result_mk_ok(lean::mk_string(triple));
  
}


// opaque targetMachineEmitToFile (targetMachine: @&Ptr TargetMachine) (module: @&Ptr Module) (filepath: @&String) (codegenType: @&UInt64): IO Unit
extern "C" LEAN_EXPORT lean_object *
lean_llvm_target_machine_emit_to_file(lean_object *target_machine,
				      lean_object *module,
				      lean_object *filepath,
				      uint64_t codegenType,
				      lean_object* /* w */) {
    // TODO (bollu): move this to a different function
    /*
    LLVMInitializeAllTargetInfos();
    LLVMInitializeAllTargets();
    LLVMInitializeAllTargetMCs();
    LLVMInitializeAllAsmParsers();
    LLVMInitializeAllAsmPrinters();
    */

    // TODO (bollu): figure out a story for cross-compilation.
    // We currently choose not to invoke LLVMInitializeAllTargetInfos() etc.
    // since our build system only enables certain backends.
    // LLVMInitializeNativeTargetInfo();
    LLVMInitializeNativeTarget();
    // LLVMInitializeNativeTargetMC();
    LLVMInitializeNativeAsmParser();
    LLVMInitializeNativeAsmPrinter();
  
    if (LLVM_DEBUG) {
      fprintf(stderr, "%s ; target_machine: %p \n", __PRETTY_FUNCTION__, lean_to_TargetMachine(target_machine));
      fprintf(stderr, "...%s ; module: %p \n", __PRETTY_FUNCTION__, lean_to_Module(module));
      fprintf(stderr, "...%s ; filepath: %s \n", __PRETTY_FUNCTION__, lean_string_cstr(filepath));
      fprintf(stderr, "...%s ; codegenType: %lu \n", __PRETTY_FUNCTION__, codegenType);
    }
    char *err_msg = NULL;
    char *filepath_c_str = strdup(lean_string_cstr(filepath)); // TODO(bollu): do we need the `strdup`?
    // LLVMTargetMachineEmitToFile(LLVMTargetMachineRef T, LLVMModuleRef M, char *Filename, LLVMCodeGenFileType codegen, char **ErrorMessage)
    int is_error = LLVMTargetMachineEmitToFile(lean_to_TargetMachine(target_machine),
				lean_to_Module(module),
				filepath_c_str,
				LLVMCodeGenFileType(codegenType),
				&err_msg);

    if (LLVM_DEBUG) {
      fprintf(stderr, "...%s ; error?: %d \n", __PRETTY_FUNCTION__, is_error);
    }

    if (LLVM_DEBUG && is_error) {
      fprintf(stderr, "...%s ; err_msg: %s \n", __PRETTY_FUNCTION__, err_msg);
    }

    
    return lean_io_result_mk_ok(lean_box(0));
  
}
