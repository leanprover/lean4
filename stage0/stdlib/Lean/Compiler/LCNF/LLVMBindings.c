// Lean compiler output
// Module: Lean.Compiler.LCNF.LLVMBindings
// Imports: public import Init.System.IO
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint64_t l_LLVM_CodegenFileType_AssemblyFile;
LEAN_EXPORT uint64_t l_LLVM_CodegenFileType_ObjectFile;
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_EQ;
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_NE;
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_UGT;
LEAN_EXPORT uint64_t l_LLVM_AttributeIndex_AttributeReturnIndex;
LEAN_EXPORT uint64_t l_LLVM_AttributeIndex_AttributeFunctionIndex;
LEAN_EXPORT uint8_t l_LLVM_Value_isNull___redArg(size_t);
LEAN_EXPORT lean_object* l_LLVM_Value_isNull___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_LLVM_Value_isNull(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_Value_isNull___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_get_value_name2(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_Value_getName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_initialize_target_info();
LEAN_EXPORT lean_object* l_LLVM_llvmInitializeTargetInfo___boxed(lean_object*);
size_t lean_llvm_create_context();
LEAN_EXPORT lean_object* l_LLVM_createContext___boxed(lean_object*);
size_t lean_llvm_create_module(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createModule___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_module_to_string(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_moduleToString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_write_bitcode_to_file(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_writeBitcodeToFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_add_function(size_t, size_t, lean_object*, size_t);
LEAN_EXPORT lean_object* l_LLVM_addFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_first_function(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getFirstFunction___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_next_function(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getNextFunction___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_named_function(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getNamedFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_add_global(size_t, size_t, lean_object*, size_t);
LEAN_EXPORT lean_object* l_LLVM_addGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_named_global(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getNamedGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_first_global(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getFirstGlobal___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_next_global(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getNextGlobal___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_global_string(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildGlobalString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t llvm_is_declaration(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_isDeclaration___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_set_initializer(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_setInitializer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_function_type(size_t, size_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_functionType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_void_type_in_context(size_t);
LEAN_EXPORT lean_object* l_LLVM_voidType___boxed(lean_object*, lean_object*);
size_t lean_llvm_int_type_in_context(size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_intTypeInContext___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_opaque_pointer_type_in_context(size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_opaquePointerTypeInContext___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_float_type_in_context(size_t);
LEAN_EXPORT lean_object* l_LLVM_floatTypeInContext___boxed(lean_object*, lean_object*);
size_t lean_llvm_double_type_in_context(size_t);
LEAN_EXPORT lean_object* l_LLVM_doubleTypeInContext___boxed(lean_object*, lean_object*);
size_t lean_llvm_pointer_type(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_pointerType___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_array_type(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_arrayType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_array(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_struct_type_in_context(size_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_structTypeInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_struct_create_named(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_structCreateNamed___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_struct_set_body(size_t, size_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_structSetBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_struct_in_context(size_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constStructInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_named_struct(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constNamedStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_set_global_constant(size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_setGlobalConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_int_to_ptr(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_constIntToPtr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_bit_cast(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_constBitCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_string(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constString___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_pointer_null(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_constPointerNull___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_undef(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getUndef___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_create_builder_in_context(size_t);
LEAN_EXPORT lean_object* l_LLVM_createBuilderInContext___boxed(lean_object*, lean_object*);
size_t lean_llvm_append_basic_block_in_context(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_appendBasicBlockInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_llvm_count_basic_blocks(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_countBasicBlocks___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_entry_basic_block(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getEntryBasicBlock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_first_instruction(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getFirstInstruction___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_position_builder_before(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_positionBuilderBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_position_builder_at_end(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_positionBuilderAtEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_call2(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildCall2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_set_tail_call(size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_setTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_TailCallKind_none;
LEAN_EXPORT uint64_t l_LLVM_TailCallKind_tail;
LEAN_EXPORT uint64_t l_LLVM_TailCallKind_mustTail;
LEAN_EXPORT uint64_t l_LLVM_TailCallKind_noTail;
lean_object* lean_llvm_set_tail_call_kind(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_setTailCallKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_cond_br(size_t, size_t, size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildCondBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_br(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_alloca(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildAlloca___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_load2(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildLoad2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_store(size_t, size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildStore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_ret(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildRet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_unreachable(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildUnreachable___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_gep2(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildGEP2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_inbounds_gep2(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildInBoundsGEP2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_sext(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_zext(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildZext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_sext_or_trunc(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSextOrTrunc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_switch(size_t, size_t, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_buildSwitch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_ptr_to_int(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildPtrToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_mul(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_add(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_sub(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_not(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_build_icmp(size_t, size_t, uint64_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildICmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_add_case(size_t, size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_addCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_insert_block(lean_object*, size_t);
LEAN_EXPORT lean_object* l_LLVM_getInsertBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_clear_insertion_position(lean_object*, size_t);
LEAN_EXPORT lean_object* l_LLVM_clearInsertionPosition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_get_basic_block_parent(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_getBasicBlockParent___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_type_of(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_typeOf___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_const_int(size_t, size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_print_module_to_string(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_printModuletoString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_print_module_to_file(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_printModuletoFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t llvm_count_params(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_countParams___boxed(lean_object*, lean_object*, lean_object*);
size_t llvm_get_param(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_getParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_llvm_create_memory_buffer_with_contents_of_file(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createMemoryBufferWithContentsOfFile___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_parse_bitcode(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_parseBitcode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_link_modules(size_t, size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_linkModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_default_target_triple();
LEAN_EXPORT lean_object* l_LLVM_getDefaultTargetTriple___boxed(lean_object*);
size_t lean_llvm_get_target_from_triple(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getTargetFromTriple___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_create_target_machine(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createTargetMachine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_target_machine_emit_to_file(size_t, size_t, size_t, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_targetMachineEmitToFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_dispose_target_machine(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_disposeTargetMachine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_dispose_module(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_disposeModule___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_verify_module(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_verifyModule___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_llvm_create_string_attribute(size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createStringAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_add_attribute_at_index(size_t, size_t, uint64_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_addAttributeAtIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_Visibility_default;
LEAN_EXPORT uint64_t l_LLVM_Visibility_hidden;
LEAN_EXPORT uint64_t l_LLVM_Visibility_protected;
lean_object* lean_llvm_set_visibility(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_setVisibility___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_DLLStorageClass_default;
LEAN_EXPORT uint64_t l_LLVM_DLLStorageClass_import;
LEAN_EXPORT uint64_t l_LLVM_DLLStorageClass_export;
lean_object* lean_llvm_set_dll_storage_class(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_setDLLStorageClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_Linkage_external;
LEAN_EXPORT uint64_t l_LLVM_Linkage_availableExternally;
LEAN_EXPORT uint64_t l_LLVM_Linkage_linkOnceAny;
LEAN_EXPORT uint64_t l_LLVM_Linkage_linkOnceODR;
LEAN_EXPORT uint64_t l_LLVM_Linkage_linkOnceODRAutoHide;
LEAN_EXPORT uint64_t l_LLVM_Linkage_weakAny;
LEAN_EXPORT uint64_t l_LLVM_Linkage_weakODR;
LEAN_EXPORT uint64_t l_LLVM_Linkage_appending;
LEAN_EXPORT uint64_t l_LLVM_Linkage_internal;
LEAN_EXPORT uint64_t l_LLVM_Linkage_private;
LEAN_EXPORT uint64_t l_LLVM_Linkage_dllImport;
LEAN_EXPORT uint64_t l_LLVM_Linkage_dllExport;
LEAN_EXPORT uint64_t l_LLVM_Linkage_externalWeak;
LEAN_EXPORT uint64_t l_LLVM_Linkage_ghost;
LEAN_EXPORT uint64_t l_LLVM_Linkage_common;
LEAN_EXPORT uint64_t l_LLVM_Linkage_linkerPrivate;
LEAN_EXPORT uint64_t l_LLVM_Linkage_linkerPrivateWeak;
lean_object* lean_llvm_set_linkage(size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_LLVM_setLinkage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i1Type(size_t);
LEAN_EXPORT lean_object* l_LLVM_i1Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i8Type(size_t);
LEAN_EXPORT lean_object* l_LLVM_i8Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i16Type(size_t);
LEAN_EXPORT lean_object* l_LLVM_i16Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i32Type(size_t);
LEAN_EXPORT lean_object* l_LLVM_i32Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i64Type(size_t);
LEAN_EXPORT lean_object* l_LLVM_i64Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_voidPtrType(size_t);
LEAN_EXPORT lean_object* l_LLVM_voidPtrType___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_i8PtrType(size_t);
LEAN_EXPORT lean_object* l_LLVM_i8PtrType___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constTrue(size_t);
LEAN_EXPORT lean_object* l_LLVM_constTrue___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constFalse(size_t);
LEAN_EXPORT lean_object* l_LLVM_constFalse___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constInt_x27(size_t, uint64_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constInt1(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constInt8(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constInt32(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constInt64(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constInt64___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constIntSizeT(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constIntSizeT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_LLVM_constIntUnsigned(size_t, uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l_LLVM_CodegenFileType_AssemblyFile(void){
_start:
{
uint64_t v___x_1_; 
v___x_1_ = 0ULL;
return v___x_1_;
}
}
static uint64_t _init_l_LLVM_CodegenFileType_ObjectFile(void){
_start:
{
uint64_t v___x_2_; 
v___x_2_ = 1ULL;
return v___x_2_;
}
}
static uint64_t _init_l_LLVM_IntPredicate_EQ(void){
_start:
{
uint64_t v___x_3_; 
v___x_3_ = 32ULL;
return v___x_3_;
}
}
static uint64_t _init_l_LLVM_IntPredicate_NE(void){
_start:
{
uint64_t v___x_4_; 
v___x_4_ = 33ULL;
return v___x_4_;
}
}
static uint64_t _init_l_LLVM_IntPredicate_UGT(void){
_start:
{
uint64_t v___x_5_; 
v___x_5_ = 34ULL;
return v___x_5_;
}
}
static uint64_t _init_l_LLVM_AttributeIndex_AttributeReturnIndex(void){
_start:
{
uint64_t v___x_6_; 
v___x_6_ = 0ULL;
return v___x_6_;
}
}
static uint64_t _init_l_LLVM_AttributeIndex_AttributeFunctionIndex(void){
_start:
{
uint64_t v___x_7_; 
v___x_7_ = 18446744073709551615ULL;
return v___x_7_;
}
}
LEAN_EXPORT uint8_t l_LLVM_Value_isNull___redArg(size_t v_v_8_){
_start:
{
size_t v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((size_t)0ULL);
v___x_10_ = lean_usize_dec_eq(v_v_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_LLVM_Value_isNull___redArg___boxed(lean_object* v_v_11_){
_start:
{
size_t v_v_boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_v_boxed_12_ = lean_unbox_usize(v_v_11_);
lean_dec(v_v_11_);
v_res_13_ = l_LLVM_Value_isNull___redArg(v_v_boxed_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l_LLVM_Value_isNull(size_t v_ctx_15_, size_t v_v_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_LLVM_Value_isNull___redArg(v_v_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_LLVM_Value_isNull___boxed(lean_object* v_ctx_18_, lean_object* v_v_19_){
_start:
{
size_t v_ctx_boxed_20_; size_t v_v_boxed_21_; uint8_t v_res_22_; lean_object* v_r_23_; 
v_ctx_boxed_20_ = lean_unbox_usize(v_ctx_18_);
lean_dec(v_ctx_18_);
v_v_boxed_21_ = lean_unbox_usize(v_v_19_);
lean_dec(v_v_19_);
v_res_22_ = l_LLVM_Value_isNull(v_ctx_boxed_20_, v_v_boxed_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_LLVM_Value_getName___boxed(lean_object* v_ctx_27_, lean_object* v_value_28_, lean_object* v_a_00___x40___internal___hyg_29_){
_start:
{
size_t v_ctx_boxed_30_; size_t v_value_boxed_31_; lean_object* v_res_32_; 
v_ctx_boxed_30_ = lean_unbox_usize(v_ctx_27_);
lean_dec(v_ctx_27_);
v_value_boxed_31_ = lean_unbox_usize(v_value_28_);
lean_dec(v_value_28_);
v_res_32_ = lean_llvm_get_value_name2(v_ctx_boxed_30_, v_value_boxed_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_LLVM_llvmInitializeTargetInfo___boxed(lean_object* v_a_00___x40___internal___hyg_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lean_llvm_initialize_target_info();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createContext___boxed(lean_object* v_a_00___x40___internal___hyg_37_){
_start:
{
size_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = lean_llvm_create_context();
v_r_39_ = lean_box_usize(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createModule___boxed(lean_object* v_ctx_43_, lean_object* v_name_44_, lean_object* v_a_00___x40___internal___hyg_45_){
_start:
{
size_t v_ctx_boxed_46_; size_t v_res_47_; lean_object* v_r_48_; 
v_ctx_boxed_46_ = lean_unbox_usize(v_ctx_43_);
lean_dec(v_ctx_43_);
v_res_47_ = lean_llvm_create_module(v_ctx_boxed_46_, v_name_44_);
lean_dec_ref(v_name_44_);
v_r_48_ = lean_box_usize(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_LLVM_moduleToString___boxed(lean_object* v_ctx_52_, lean_object* v_m_53_, lean_object* v_a_00___x40___internal___hyg_54_){
_start:
{
size_t v_ctx_boxed_55_; size_t v_m_boxed_56_; lean_object* v_res_57_; 
v_ctx_boxed_55_ = lean_unbox_usize(v_ctx_52_);
lean_dec(v_ctx_52_);
v_m_boxed_56_ = lean_unbox_usize(v_m_53_);
lean_dec(v_m_53_);
v_res_57_ = lean_llvm_module_to_string(v_ctx_boxed_55_, v_m_boxed_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_LLVM_writeBitcodeToFile___boxed(lean_object* v_ctx_62_, lean_object* v_m_63_, lean_object* v_path_64_, lean_object* v_a_00___x40___internal___hyg_65_){
_start:
{
size_t v_ctx_boxed_66_; size_t v_m_boxed_67_; lean_object* v_res_68_; 
v_ctx_boxed_66_ = lean_unbox_usize(v_ctx_62_);
lean_dec(v_ctx_62_);
v_m_boxed_67_ = lean_unbox_usize(v_m_63_);
lean_dec(v_m_63_);
v_res_68_ = lean_llvm_write_bitcode_to_file(v_ctx_boxed_66_, v_m_boxed_67_, v_path_64_);
lean_dec_ref(v_path_64_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addFunction___boxed(lean_object* v_ctx_74_, lean_object* v_m_75_, lean_object* v_name_76_, lean_object* v_type_77_, lean_object* v_a_00___x40___internal___hyg_78_){
_start:
{
size_t v_ctx_boxed_79_; size_t v_m_boxed_80_; size_t v_type_boxed_81_; size_t v_res_82_; lean_object* v_r_83_; 
v_ctx_boxed_79_ = lean_unbox_usize(v_ctx_74_);
lean_dec(v_ctx_74_);
v_m_boxed_80_ = lean_unbox_usize(v_m_75_);
lean_dec(v_m_75_);
v_type_boxed_81_ = lean_unbox_usize(v_type_77_);
lean_dec(v_type_77_);
v_res_82_ = lean_llvm_add_function(v_ctx_boxed_79_, v_m_boxed_80_, v_name_76_, v_type_boxed_81_);
lean_dec_ref(v_name_76_);
v_r_83_ = lean_box_usize(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getFirstFunction___boxed(lean_object* v_ctx_87_, lean_object* v_m_88_, lean_object* v_a_00___x40___internal___hyg_89_){
_start:
{
size_t v_ctx_boxed_90_; size_t v_m_boxed_91_; size_t v_res_92_; lean_object* v_r_93_; 
v_ctx_boxed_90_ = lean_unbox_usize(v_ctx_87_);
lean_dec(v_ctx_87_);
v_m_boxed_91_ = lean_unbox_usize(v_m_88_);
lean_dec(v_m_88_);
v_res_92_ = lean_llvm_get_first_function(v_ctx_boxed_90_, v_m_boxed_91_);
v_r_93_ = lean_box_usize(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNextFunction___boxed(lean_object* v_ctx_97_, lean_object* v_glbl_98_, lean_object* v_a_00___x40___internal___hyg_99_){
_start:
{
size_t v_ctx_boxed_100_; size_t v_glbl_boxed_101_; size_t v_res_102_; lean_object* v_r_103_; 
v_ctx_boxed_100_ = lean_unbox_usize(v_ctx_97_);
lean_dec(v_ctx_97_);
v_glbl_boxed_101_ = lean_unbox_usize(v_glbl_98_);
lean_dec(v_glbl_98_);
v_res_102_ = lean_llvm_get_next_function(v_ctx_boxed_100_, v_glbl_boxed_101_);
v_r_103_ = lean_box_usize(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNamedFunction___boxed(lean_object* v_ctx_108_, lean_object* v_m_109_, lean_object* v_name_110_, lean_object* v_a_00___x40___internal___hyg_111_){
_start:
{
size_t v_ctx_boxed_112_; size_t v_m_boxed_113_; lean_object* v_res_114_; 
v_ctx_boxed_112_ = lean_unbox_usize(v_ctx_108_);
lean_dec(v_ctx_108_);
v_m_boxed_113_ = lean_unbox_usize(v_m_109_);
lean_dec(v_m_109_);
v_res_114_ = lean_llvm_get_named_function(v_ctx_boxed_112_, v_m_boxed_113_, v_name_110_);
lean_dec_ref(v_name_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addGlobal___boxed(lean_object* v_ctx_120_, lean_object* v_m_121_, lean_object* v_name_122_, lean_object* v_type_123_, lean_object* v_a_00___x40___internal___hyg_124_){
_start:
{
size_t v_ctx_boxed_125_; size_t v_m_boxed_126_; size_t v_type_boxed_127_; size_t v_res_128_; lean_object* v_r_129_; 
v_ctx_boxed_125_ = lean_unbox_usize(v_ctx_120_);
lean_dec(v_ctx_120_);
v_m_boxed_126_ = lean_unbox_usize(v_m_121_);
lean_dec(v_m_121_);
v_type_boxed_127_ = lean_unbox_usize(v_type_123_);
lean_dec(v_type_123_);
v_res_128_ = lean_llvm_add_global(v_ctx_boxed_125_, v_m_boxed_126_, v_name_122_, v_type_boxed_127_);
lean_dec_ref(v_name_122_);
v_r_129_ = lean_box_usize(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNamedGlobal___boxed(lean_object* v_ctx_134_, lean_object* v_m_135_, lean_object* v_name_136_, lean_object* v_a_00___x40___internal___hyg_137_){
_start:
{
size_t v_ctx_boxed_138_; size_t v_m_boxed_139_; lean_object* v_res_140_; 
v_ctx_boxed_138_ = lean_unbox_usize(v_ctx_134_);
lean_dec(v_ctx_134_);
v_m_boxed_139_ = lean_unbox_usize(v_m_135_);
lean_dec(v_m_135_);
v_res_140_ = lean_llvm_get_named_global(v_ctx_boxed_138_, v_m_boxed_139_, v_name_136_);
lean_dec_ref(v_name_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getFirstGlobal___boxed(lean_object* v_ctx_144_, lean_object* v_m_145_, lean_object* v_a_00___x40___internal___hyg_146_){
_start:
{
size_t v_ctx_boxed_147_; size_t v_m_boxed_148_; size_t v_res_149_; lean_object* v_r_150_; 
v_ctx_boxed_147_ = lean_unbox_usize(v_ctx_144_);
lean_dec(v_ctx_144_);
v_m_boxed_148_ = lean_unbox_usize(v_m_145_);
lean_dec(v_m_145_);
v_res_149_ = lean_llvm_get_first_global(v_ctx_boxed_147_, v_m_boxed_148_);
v_r_150_ = lean_box_usize(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNextGlobal___boxed(lean_object* v_ctx_154_, lean_object* v_glbl_155_, lean_object* v_a_00___x40___internal___hyg_156_){
_start:
{
size_t v_ctx_boxed_157_; size_t v_glbl_boxed_158_; size_t v_res_159_; lean_object* v_r_160_; 
v_ctx_boxed_157_ = lean_unbox_usize(v_ctx_154_);
lean_dec(v_ctx_154_);
v_glbl_boxed_158_ = lean_unbox_usize(v_glbl_155_);
lean_dec(v_glbl_155_);
v_res_159_ = lean_llvm_get_next_global(v_ctx_boxed_157_, v_glbl_boxed_158_);
v_r_160_ = lean_box_usize(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildGlobalString___boxed(lean_object* v_ctx_166_, lean_object* v_builder_167_, lean_object* v_value_168_, lean_object* v_name_169_, lean_object* v_a_00___x40___internal___hyg_170_){
_start:
{
size_t v_ctx_boxed_171_; size_t v_builder_boxed_172_; size_t v_res_173_; lean_object* v_r_174_; 
v_ctx_boxed_171_ = lean_unbox_usize(v_ctx_166_);
lean_dec(v_ctx_166_);
v_builder_boxed_172_ = lean_unbox_usize(v_builder_167_);
lean_dec(v_builder_167_);
v_res_173_ = lean_llvm_build_global_string(v_ctx_boxed_171_, v_builder_boxed_172_, v_value_168_, v_name_169_);
lean_dec_ref(v_value_168_);
v_r_174_ = lean_box_usize(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_LLVM_isDeclaration___boxed(lean_object* v_ctx_178_, lean_object* v_global_179_, lean_object* v_a_00___x40___internal___hyg_180_){
_start:
{
size_t v_ctx_boxed_181_; size_t v_global_boxed_182_; uint8_t v_res_183_; lean_object* v_r_184_; 
v_ctx_boxed_181_ = lean_unbox_usize(v_ctx_178_);
lean_dec(v_ctx_178_);
v_global_boxed_182_ = lean_unbox_usize(v_global_179_);
lean_dec(v_global_179_);
v_res_183_ = llvm_is_declaration(v_ctx_boxed_181_, v_global_boxed_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setInitializer___boxed(lean_object* v_ctx_189_, lean_object* v_glbl_190_, lean_object* v_val_191_, lean_object* v_a_00___x40___internal___hyg_192_){
_start:
{
size_t v_ctx_boxed_193_; size_t v_glbl_boxed_194_; size_t v_val_boxed_195_; lean_object* v_res_196_; 
v_ctx_boxed_193_ = lean_unbox_usize(v_ctx_189_);
lean_dec(v_ctx_189_);
v_glbl_boxed_194_ = lean_unbox_usize(v_glbl_190_);
lean_dec(v_glbl_190_);
v_val_boxed_195_ = lean_unbox_usize(v_val_191_);
lean_dec(v_val_191_);
v_res_196_ = lean_llvm_set_initializer(v_ctx_boxed_193_, v_glbl_boxed_194_, v_val_boxed_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_LLVM_functionType___boxed(lean_object* v_ctx_202_, lean_object* v_retty_203_, lean_object* v_args_204_, lean_object* v_isVarArg_205_, lean_object* v_a_00___x40___internal___hyg_206_){
_start:
{
size_t v_ctx_boxed_207_; size_t v_retty_boxed_208_; uint8_t v_isVarArg_boxed_209_; size_t v_res_210_; lean_object* v_r_211_; 
v_ctx_boxed_207_ = lean_unbox_usize(v_ctx_202_);
lean_dec(v_ctx_202_);
v_retty_boxed_208_ = lean_unbox_usize(v_retty_203_);
lean_dec(v_retty_203_);
v_isVarArg_boxed_209_ = lean_unbox(v_isVarArg_205_);
v_res_210_ = lean_llvm_function_type(v_ctx_boxed_207_, v_retty_boxed_208_, v_args_204_, v_isVarArg_boxed_209_);
lean_dec_ref(v_args_204_);
v_r_211_ = lean_box_usize(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_LLVM_voidType___boxed(lean_object* v_ctx_214_, lean_object* v_a_00___x40___internal___hyg_215_){
_start:
{
size_t v_ctx_boxed_216_; size_t v_res_217_; lean_object* v_r_218_; 
v_ctx_boxed_216_ = lean_unbox_usize(v_ctx_214_);
lean_dec(v_ctx_214_);
v_res_217_ = lean_llvm_void_type_in_context(v_ctx_boxed_216_);
v_r_218_ = lean_box_usize(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_LLVM_intTypeInContext___boxed(lean_object* v_ctx_222_, lean_object* v_width_223_, lean_object* v_a_00___x40___internal___hyg_224_){
_start:
{
size_t v_ctx_boxed_225_; uint64_t v_width_boxed_226_; size_t v_res_227_; lean_object* v_r_228_; 
v_ctx_boxed_225_ = lean_unbox_usize(v_ctx_222_);
lean_dec(v_ctx_222_);
v_width_boxed_226_ = lean_unbox_uint64(v_width_223_);
lean_dec_ref(v_width_223_);
v_res_227_ = lean_llvm_int_type_in_context(v_ctx_boxed_225_, v_width_boxed_226_);
v_r_228_ = lean_box_usize(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l_LLVM_opaquePointerTypeInContext___boxed(lean_object* v_ctx_232_, lean_object* v_addrspace_233_, lean_object* v_a_00___x40___internal___hyg_234_){
_start:
{
size_t v_ctx_boxed_235_; uint64_t v_addrspace_boxed_236_; size_t v_res_237_; lean_object* v_r_238_; 
v_ctx_boxed_235_ = lean_unbox_usize(v_ctx_232_);
lean_dec(v_ctx_232_);
v_addrspace_boxed_236_ = lean_unbox_uint64(v_addrspace_233_);
lean_dec_ref(v_addrspace_233_);
v_res_237_ = lean_llvm_opaque_pointer_type_in_context(v_ctx_boxed_235_, v_addrspace_boxed_236_);
v_r_238_ = lean_box_usize(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_LLVM_floatTypeInContext___boxed(lean_object* v_ctx_241_, lean_object* v_a_00___x40___internal___hyg_242_){
_start:
{
size_t v_ctx_boxed_243_; size_t v_res_244_; lean_object* v_r_245_; 
v_ctx_boxed_243_ = lean_unbox_usize(v_ctx_241_);
lean_dec(v_ctx_241_);
v_res_244_ = lean_llvm_float_type_in_context(v_ctx_boxed_243_);
v_r_245_ = lean_box_usize(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_LLVM_doubleTypeInContext___boxed(lean_object* v_ctx_248_, lean_object* v_a_00___x40___internal___hyg_249_){
_start:
{
size_t v_ctx_boxed_250_; size_t v_res_251_; lean_object* v_r_252_; 
v_ctx_boxed_250_ = lean_unbox_usize(v_ctx_248_);
lean_dec(v_ctx_248_);
v_res_251_ = lean_llvm_double_type_in_context(v_ctx_boxed_250_);
v_r_252_ = lean_box_usize(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_LLVM_pointerType___boxed(lean_object* v_ctx_256_, lean_object* v_elemty_257_, lean_object* v_a_00___x40___internal___hyg_258_){
_start:
{
size_t v_ctx_boxed_259_; size_t v_elemty_boxed_260_; size_t v_res_261_; lean_object* v_r_262_; 
v_ctx_boxed_259_ = lean_unbox_usize(v_ctx_256_);
lean_dec(v_ctx_256_);
v_elemty_boxed_260_ = lean_unbox_usize(v_elemty_257_);
lean_dec(v_elemty_257_);
v_res_261_ = lean_llvm_pointer_type(v_ctx_boxed_259_, v_elemty_boxed_260_);
v_r_262_ = lean_box_usize(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_LLVM_arrayType___boxed(lean_object* v_ctx_267_, lean_object* v_elemty_268_, lean_object* v_nelem_269_, lean_object* v_a_00___x40___internal___hyg_270_){
_start:
{
size_t v_ctx_boxed_271_; size_t v_elemty_boxed_272_; uint64_t v_nelem_boxed_273_; size_t v_res_274_; lean_object* v_r_275_; 
v_ctx_boxed_271_ = lean_unbox_usize(v_ctx_267_);
lean_dec(v_ctx_267_);
v_elemty_boxed_272_ = lean_unbox_usize(v_elemty_268_);
lean_dec(v_elemty_268_);
v_nelem_boxed_273_ = lean_unbox_uint64(v_nelem_269_);
lean_dec_ref(v_nelem_269_);
v_res_274_ = lean_llvm_array_type(v_ctx_boxed_271_, v_elemty_boxed_272_, v_nelem_boxed_273_);
v_r_275_ = lean_box_usize(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constArray___boxed(lean_object* v_ctx_280_, lean_object* v_elemty_281_, lean_object* v_vals_282_, lean_object* v_a_00___x40___internal___hyg_283_){
_start:
{
size_t v_ctx_boxed_284_; size_t v_elemty_boxed_285_; size_t v_res_286_; lean_object* v_r_287_; 
v_ctx_boxed_284_ = lean_unbox_usize(v_ctx_280_);
lean_dec(v_ctx_280_);
v_elemty_boxed_285_ = lean_unbox_usize(v_elemty_281_);
lean_dec(v_elemty_281_);
v_res_286_ = lean_llvm_const_array(v_ctx_boxed_284_, v_elemty_boxed_285_, v_vals_282_);
lean_dec_ref(v_vals_282_);
v_r_287_ = lean_box_usize(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT lean_object* l_LLVM_structTypeInContext___boxed(lean_object* v_ctx_292_, lean_object* v_elemTys_293_, lean_object* v_packed_294_, lean_object* v_a_00___x40___internal___hyg_295_){
_start:
{
size_t v_ctx_boxed_296_; uint8_t v_packed_boxed_297_; size_t v_res_298_; lean_object* v_r_299_; 
v_ctx_boxed_296_ = lean_unbox_usize(v_ctx_292_);
lean_dec(v_ctx_292_);
v_packed_boxed_297_ = lean_unbox(v_packed_294_);
v_res_298_ = lean_llvm_struct_type_in_context(v_ctx_boxed_296_, v_elemTys_293_, v_packed_boxed_297_);
lean_dec_ref(v_elemTys_293_);
v_r_299_ = lean_box_usize(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_LLVM_structCreateNamed___boxed(lean_object* v_ctx_303_, lean_object* v_name_304_, lean_object* v_a_00___x40___internal___hyg_305_){
_start:
{
size_t v_ctx_boxed_306_; size_t v_res_307_; lean_object* v_r_308_; 
v_ctx_boxed_306_ = lean_unbox_usize(v_ctx_303_);
lean_dec(v_ctx_303_);
v_res_307_ = lean_llvm_struct_create_named(v_ctx_boxed_306_, v_name_304_);
lean_dec_ref(v_name_304_);
v_r_308_ = lean_box_usize(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_LLVM_structSetBody___boxed(lean_object* v_ctx_314_, lean_object* v_ty_315_, lean_object* v_elemTys_316_, lean_object* v_packed_317_, lean_object* v_a_00___x40___internal___hyg_318_){
_start:
{
size_t v_ctx_boxed_319_; size_t v_ty_boxed_320_; uint8_t v_packed_boxed_321_; lean_object* v_res_322_; 
v_ctx_boxed_319_ = lean_unbox_usize(v_ctx_314_);
lean_dec(v_ctx_314_);
v_ty_boxed_320_ = lean_unbox_usize(v_ty_315_);
lean_dec(v_ty_315_);
v_packed_boxed_321_ = lean_unbox(v_packed_317_);
v_res_322_ = lean_llvm_struct_set_body(v_ctx_boxed_319_, v_ty_boxed_320_, v_elemTys_316_, v_packed_boxed_321_);
lean_dec_ref(v_elemTys_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constStructInContext___boxed(lean_object* v_ctx_327_, lean_object* v_vals_328_, lean_object* v_packed_329_, lean_object* v_a_00___x40___internal___hyg_330_){
_start:
{
size_t v_ctx_boxed_331_; uint8_t v_packed_boxed_332_; size_t v_res_333_; lean_object* v_r_334_; 
v_ctx_boxed_331_ = lean_unbox_usize(v_ctx_327_);
lean_dec(v_ctx_327_);
v_packed_boxed_332_ = lean_unbox(v_packed_329_);
v_res_333_ = lean_llvm_const_struct_in_context(v_ctx_boxed_331_, v_vals_328_, v_packed_boxed_332_);
lean_dec_ref(v_vals_328_);
v_r_334_ = lean_box_usize(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constNamedStruct___boxed(lean_object* v_ctx_339_, lean_object* v_ty_340_, lean_object* v_vals_341_, lean_object* v_a_00___x40___internal___hyg_342_){
_start:
{
size_t v_ctx_boxed_343_; size_t v_ty_boxed_344_; size_t v_res_345_; lean_object* v_r_346_; 
v_ctx_boxed_343_ = lean_unbox_usize(v_ctx_339_);
lean_dec(v_ctx_339_);
v_ty_boxed_344_ = lean_unbox_usize(v_ty_340_);
lean_dec(v_ty_340_);
v_res_345_ = lean_llvm_const_named_struct(v_ctx_boxed_343_, v_ty_boxed_344_, v_vals_341_);
lean_dec_ref(v_vals_341_);
v_r_346_ = lean_box_usize(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setGlobalConstant___boxed(lean_object* v_ctx_351_, lean_object* v_glbl_352_, lean_object* v_isConst_353_, lean_object* v_a_00___x40___internal___hyg_354_){
_start:
{
size_t v_ctx_boxed_355_; size_t v_glbl_boxed_356_; uint8_t v_isConst_boxed_357_; lean_object* v_res_358_; 
v_ctx_boxed_355_ = lean_unbox_usize(v_ctx_351_);
lean_dec(v_ctx_351_);
v_glbl_boxed_356_ = lean_unbox_usize(v_glbl_352_);
lean_dec(v_glbl_352_);
v_isConst_boxed_357_ = lean_unbox(v_isConst_353_);
v_res_358_ = lean_llvm_set_global_constant(v_ctx_boxed_355_, v_glbl_boxed_356_, v_isConst_boxed_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntToPtr___boxed(lean_object* v_ctx_363_, lean_object* v_val_364_, lean_object* v_destTy_365_, lean_object* v_a_00___x40___internal___hyg_366_){
_start:
{
size_t v_ctx_boxed_367_; size_t v_val_boxed_368_; size_t v_destTy_boxed_369_; size_t v_res_370_; lean_object* v_r_371_; 
v_ctx_boxed_367_ = lean_unbox_usize(v_ctx_363_);
lean_dec(v_ctx_363_);
v_val_boxed_368_ = lean_unbox_usize(v_val_364_);
lean_dec(v_val_364_);
v_destTy_boxed_369_ = lean_unbox_usize(v_destTy_365_);
lean_dec(v_destTy_365_);
v_res_370_ = lean_llvm_const_int_to_ptr(v_ctx_boxed_367_, v_val_boxed_368_, v_destTy_boxed_369_);
v_r_371_ = lean_box_usize(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constBitCast___boxed(lean_object* v_ctx_376_, lean_object* v_val_377_, lean_object* v_destTy_378_, lean_object* v_a_00___x40___internal___hyg_379_){
_start:
{
size_t v_ctx_boxed_380_; size_t v_val_boxed_381_; size_t v_destTy_boxed_382_; size_t v_res_383_; lean_object* v_r_384_; 
v_ctx_boxed_380_ = lean_unbox_usize(v_ctx_376_);
lean_dec(v_ctx_376_);
v_val_boxed_381_ = lean_unbox_usize(v_val_377_);
lean_dec(v_val_377_);
v_destTy_boxed_382_ = lean_unbox_usize(v_destTy_378_);
lean_dec(v_destTy_378_);
v_res_383_ = lean_llvm_const_bit_cast(v_ctx_boxed_380_, v_val_boxed_381_, v_destTy_boxed_382_);
v_r_384_ = lean_box_usize(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constString___boxed(lean_object* v_ctx_388_, lean_object* v_str_389_, lean_object* v_a_00___x40___internal___hyg_390_){
_start:
{
size_t v_ctx_boxed_391_; size_t v_res_392_; lean_object* v_r_393_; 
v_ctx_boxed_391_ = lean_unbox_usize(v_ctx_388_);
lean_dec(v_ctx_388_);
v_res_392_ = lean_llvm_const_string(v_ctx_boxed_391_, v_str_389_);
lean_dec_ref(v_str_389_);
v_r_393_ = lean_box_usize(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constPointerNull___boxed(lean_object* v_ctx_397_, lean_object* v_elemty_398_, lean_object* v_a_00___x40___internal___hyg_399_){
_start:
{
size_t v_ctx_boxed_400_; size_t v_elemty_boxed_401_; size_t v_res_402_; lean_object* v_r_403_; 
v_ctx_boxed_400_ = lean_unbox_usize(v_ctx_397_);
lean_dec(v_ctx_397_);
v_elemty_boxed_401_ = lean_unbox_usize(v_elemty_398_);
lean_dec(v_elemty_398_);
v_res_402_ = lean_llvm_const_pointer_null(v_ctx_boxed_400_, v_elemty_boxed_401_);
v_r_403_ = lean_box_usize(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getUndef___boxed(lean_object* v_ctx_407_, lean_object* v_elemty_408_, lean_object* v_a_00___x40___internal___hyg_409_){
_start:
{
size_t v_ctx_boxed_410_; size_t v_elemty_boxed_411_; size_t v_res_412_; lean_object* v_r_413_; 
v_ctx_boxed_410_ = lean_unbox_usize(v_ctx_407_);
lean_dec(v_ctx_407_);
v_elemty_boxed_411_ = lean_unbox_usize(v_elemty_408_);
lean_dec(v_elemty_408_);
v_res_412_ = lean_llvm_get_undef(v_ctx_boxed_410_, v_elemty_boxed_411_);
v_r_413_ = lean_box_usize(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createBuilderInContext___boxed(lean_object* v_ctx_416_, lean_object* v_a_00___x40___internal___hyg_417_){
_start:
{
size_t v_ctx_boxed_418_; size_t v_res_419_; lean_object* v_r_420_; 
v_ctx_boxed_418_ = lean_unbox_usize(v_ctx_416_);
lean_dec(v_ctx_416_);
v_res_419_ = lean_llvm_create_builder_in_context(v_ctx_boxed_418_);
v_r_420_ = lean_box_usize(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_LLVM_appendBasicBlockInContext___boxed(lean_object* v_ctx_425_, lean_object* v_fn_426_, lean_object* v_name_427_, lean_object* v_a_00___x40___internal___hyg_428_){
_start:
{
size_t v_ctx_boxed_429_; size_t v_fn_boxed_430_; size_t v_res_431_; lean_object* v_r_432_; 
v_ctx_boxed_429_ = lean_unbox_usize(v_ctx_425_);
lean_dec(v_ctx_425_);
v_fn_boxed_430_ = lean_unbox_usize(v_fn_426_);
lean_dec(v_fn_426_);
v_res_431_ = lean_llvm_append_basic_block_in_context(v_ctx_boxed_429_, v_fn_boxed_430_, v_name_427_);
lean_dec_ref(v_name_427_);
v_r_432_ = lean_box_usize(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l_LLVM_countBasicBlocks___boxed(lean_object* v_ctx_436_, lean_object* v_fn_437_, lean_object* v_a_00___x40___internal___hyg_438_){
_start:
{
size_t v_ctx_boxed_439_; size_t v_fn_boxed_440_; uint64_t v_res_441_; lean_object* v_r_442_; 
v_ctx_boxed_439_ = lean_unbox_usize(v_ctx_436_);
lean_dec(v_ctx_436_);
v_fn_boxed_440_ = lean_unbox_usize(v_fn_437_);
lean_dec(v_fn_437_);
v_res_441_ = lean_llvm_count_basic_blocks(v_ctx_boxed_439_, v_fn_boxed_440_);
v_r_442_ = lean_box_uint64(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getEntryBasicBlock___boxed(lean_object* v_ctx_446_, lean_object* v_fn_447_, lean_object* v_a_00___x40___internal___hyg_448_){
_start:
{
size_t v_ctx_boxed_449_; size_t v_fn_boxed_450_; size_t v_res_451_; lean_object* v_r_452_; 
v_ctx_boxed_449_ = lean_unbox_usize(v_ctx_446_);
lean_dec(v_ctx_446_);
v_fn_boxed_450_ = lean_unbox_usize(v_fn_447_);
lean_dec(v_fn_447_);
v_res_451_ = lean_llvm_get_entry_basic_block(v_ctx_boxed_449_, v_fn_boxed_450_);
v_r_452_ = lean_box_usize(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getFirstInstruction___boxed(lean_object* v_ctx_456_, lean_object* v_bb_457_, lean_object* v_a_00___x40___internal___hyg_458_){
_start:
{
size_t v_ctx_boxed_459_; size_t v_bb_boxed_460_; lean_object* v_res_461_; 
v_ctx_boxed_459_ = lean_unbox_usize(v_ctx_456_);
lean_dec(v_ctx_456_);
v_bb_boxed_460_ = lean_unbox_usize(v_bb_457_);
lean_dec(v_bb_457_);
v_res_461_ = lean_llvm_get_first_instruction(v_ctx_boxed_459_, v_bb_boxed_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_LLVM_positionBuilderBefore___boxed(lean_object* v_ctx_466_, lean_object* v_builder_467_, lean_object* v_instr_468_, lean_object* v_a_00___x40___internal___hyg_469_){
_start:
{
size_t v_ctx_boxed_470_; size_t v_builder_boxed_471_; size_t v_instr_boxed_472_; lean_object* v_res_473_; 
v_ctx_boxed_470_ = lean_unbox_usize(v_ctx_466_);
lean_dec(v_ctx_466_);
v_builder_boxed_471_ = lean_unbox_usize(v_builder_467_);
lean_dec(v_builder_467_);
v_instr_boxed_472_ = lean_unbox_usize(v_instr_468_);
lean_dec(v_instr_468_);
v_res_473_ = lean_llvm_position_builder_before(v_ctx_boxed_470_, v_builder_boxed_471_, v_instr_boxed_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_LLVM_positionBuilderAtEnd___boxed(lean_object* v_Context_00___x40_Lean_Compiler_LCNF_LLVMBindings_2945912803____hygCtx___hyg_479_, lean_object* v_ctx_480_, lean_object* v_builder_481_, lean_object* v_bb_482_, lean_object* v_a_00___x40___internal___hyg_483_){
_start:
{
size_t v_builder_boxed_484_; size_t v_bb_boxed_485_; lean_object* v_res_486_; 
v_builder_boxed_484_ = lean_unbox_usize(v_builder_481_);
lean_dec(v_builder_481_);
v_bb_boxed_485_ = lean_unbox_usize(v_bb_482_);
lean_dec(v_bb_482_);
v_res_486_ = lean_llvm_position_builder_at_end(v_ctx_480_, v_builder_boxed_484_, v_bb_boxed_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCall2___boxed(lean_object* v_ctx_494_, lean_object* v_builder_495_, lean_object* v_ty_496_, lean_object* v_fn_497_, lean_object* v_args_498_, lean_object* v_name_499_, lean_object* v_a_00___x40___internal___hyg_500_){
_start:
{
size_t v_ctx_boxed_501_; size_t v_builder_boxed_502_; size_t v_ty_boxed_503_; size_t v_fn_boxed_504_; size_t v_res_505_; lean_object* v_r_506_; 
v_ctx_boxed_501_ = lean_unbox_usize(v_ctx_494_);
lean_dec(v_ctx_494_);
v_builder_boxed_502_ = lean_unbox_usize(v_builder_495_);
lean_dec(v_builder_495_);
v_ty_boxed_503_ = lean_unbox_usize(v_ty_496_);
lean_dec(v_ty_496_);
v_fn_boxed_504_ = lean_unbox_usize(v_fn_497_);
lean_dec(v_fn_497_);
v_res_505_ = lean_llvm_build_call2(v_ctx_boxed_501_, v_builder_boxed_502_, v_ty_boxed_503_, v_fn_boxed_504_, v_args_498_, v_name_499_);
lean_dec_ref(v_args_498_);
v_r_506_ = lean_box_usize(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setTailCall___boxed(lean_object* v_ctx_511_, lean_object* v_fn_512_, lean_object* v_istail_513_, lean_object* v_a_00___x40___internal___hyg_514_){
_start:
{
size_t v_ctx_boxed_515_; size_t v_fn_boxed_516_; uint8_t v_istail_boxed_517_; lean_object* v_res_518_; 
v_ctx_boxed_515_ = lean_unbox_usize(v_ctx_511_);
lean_dec(v_ctx_511_);
v_fn_boxed_516_ = lean_unbox_usize(v_fn_512_);
lean_dec(v_fn_512_);
v_istail_boxed_517_ = lean_unbox(v_istail_513_);
v_res_518_ = lean_llvm_set_tail_call(v_ctx_boxed_515_, v_fn_boxed_516_, v_istail_boxed_517_);
return v_res_518_;
}
}
static uint64_t _init_l_LLVM_TailCallKind_none(void){
_start:
{
uint64_t v___x_519_; 
v___x_519_ = 0ULL;
return v___x_519_;
}
}
static uint64_t _init_l_LLVM_TailCallKind_tail(void){
_start:
{
uint64_t v___x_520_; 
v___x_520_ = 1ULL;
return v___x_520_;
}
}
static uint64_t _init_l_LLVM_TailCallKind_mustTail(void){
_start:
{
uint64_t v___x_521_; 
v___x_521_ = 2ULL;
return v___x_521_;
}
}
static uint64_t _init_l_LLVM_TailCallKind_noTail(void){
_start:
{
uint64_t v___x_522_; 
v___x_522_ = 3ULL;
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setTailCallKind___boxed(lean_object* v_ctx_527_, lean_object* v_fn_528_, lean_object* v_kind_529_, lean_object* v_a_00___x40___internal___hyg_530_){
_start:
{
size_t v_ctx_boxed_531_; size_t v_fn_boxed_532_; uint64_t v_kind_boxed_533_; lean_object* v_res_534_; 
v_ctx_boxed_531_ = lean_unbox_usize(v_ctx_527_);
lean_dec(v_ctx_527_);
v_fn_boxed_532_ = lean_unbox_usize(v_fn_528_);
lean_dec(v_fn_528_);
v_kind_boxed_533_ = lean_unbox_uint64(v_kind_529_);
lean_dec_ref(v_kind_529_);
v_res_534_ = lean_llvm_set_tail_call_kind(v_ctx_boxed_531_, v_fn_boxed_532_, v_kind_boxed_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCondBr___boxed(lean_object* v_ctx_541_, lean_object* v_builder_542_, lean_object* v_if___543_, lean_object* v_thenbb_544_, lean_object* v_elsebb_545_, lean_object* v_a_00___x40___internal___hyg_546_){
_start:
{
size_t v_ctx_boxed_547_; size_t v_builder_boxed_548_; size_t v_if___00boxed_549_; size_t v_thenbb_boxed_550_; size_t v_elsebb_boxed_551_; size_t v_res_552_; lean_object* v_r_553_; 
v_ctx_boxed_547_ = lean_unbox_usize(v_ctx_541_);
lean_dec(v_ctx_541_);
v_builder_boxed_548_ = lean_unbox_usize(v_builder_542_);
lean_dec(v_builder_542_);
v_if___00boxed_549_ = lean_unbox_usize(v_if___543_);
lean_dec(v_if___543_);
v_thenbb_boxed_550_ = lean_unbox_usize(v_thenbb_544_);
lean_dec(v_thenbb_544_);
v_elsebb_boxed_551_ = lean_unbox_usize(v_elsebb_545_);
lean_dec(v_elsebb_545_);
v_res_552_ = lean_llvm_build_cond_br(v_ctx_boxed_547_, v_builder_boxed_548_, v_if___00boxed_549_, v_thenbb_boxed_550_, v_elsebb_boxed_551_);
v_r_553_ = lean_box_usize(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildBr___boxed(lean_object* v_ctx_558_, lean_object* v_builder_559_, lean_object* v_bb_560_, lean_object* v_a_00___x40___internal___hyg_561_){
_start:
{
size_t v_ctx_boxed_562_; size_t v_builder_boxed_563_; size_t v_bb_boxed_564_; size_t v_res_565_; lean_object* v_r_566_; 
v_ctx_boxed_562_ = lean_unbox_usize(v_ctx_558_);
lean_dec(v_ctx_558_);
v_builder_boxed_563_ = lean_unbox_usize(v_builder_559_);
lean_dec(v_builder_559_);
v_bb_boxed_564_ = lean_unbox_usize(v_bb_560_);
lean_dec(v_bb_560_);
v_res_565_ = lean_llvm_build_br(v_ctx_boxed_562_, v_builder_boxed_563_, v_bb_boxed_564_);
v_r_566_ = lean_box_usize(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAlloca___boxed(lean_object* v_ctx_572_, lean_object* v_builder_573_, lean_object* v_ty_574_, lean_object* v_name_575_, lean_object* v_a_00___x40___internal___hyg_576_){
_start:
{
size_t v_ctx_boxed_577_; size_t v_builder_boxed_578_; size_t v_ty_boxed_579_; size_t v_res_580_; lean_object* v_r_581_; 
v_ctx_boxed_577_ = lean_unbox_usize(v_ctx_572_);
lean_dec(v_ctx_572_);
v_builder_boxed_578_ = lean_unbox_usize(v_builder_573_);
lean_dec(v_builder_573_);
v_ty_boxed_579_ = lean_unbox_usize(v_ty_574_);
lean_dec(v_ty_574_);
v_res_580_ = lean_llvm_build_alloca(v_ctx_boxed_577_, v_builder_boxed_578_, v_ty_boxed_579_, v_name_575_);
v_r_581_ = lean_box_usize(v_res_580_);
return v_r_581_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildLoad2___boxed(lean_object* v_ctx_588_, lean_object* v_builder_589_, lean_object* v_ty_590_, lean_object* v_val_591_, lean_object* v_name_592_, lean_object* v_a_00___x40___internal___hyg_593_){
_start:
{
size_t v_ctx_boxed_594_; size_t v_builder_boxed_595_; size_t v_ty_boxed_596_; size_t v_val_boxed_597_; size_t v_res_598_; lean_object* v_r_599_; 
v_ctx_boxed_594_ = lean_unbox_usize(v_ctx_588_);
lean_dec(v_ctx_588_);
v_builder_boxed_595_ = lean_unbox_usize(v_builder_589_);
lean_dec(v_builder_589_);
v_ty_boxed_596_ = lean_unbox_usize(v_ty_590_);
lean_dec(v_ty_590_);
v_val_boxed_597_ = lean_unbox_usize(v_val_591_);
lean_dec(v_val_591_);
v_res_598_ = lean_llvm_build_load2(v_ctx_boxed_594_, v_builder_boxed_595_, v_ty_boxed_596_, v_val_boxed_597_, v_name_592_);
v_r_599_ = lean_box_usize(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildStore___boxed(lean_object* v_ctx_605_, lean_object* v_builder_606_, lean_object* v_val_607_, lean_object* v_store__loc__ptr_608_, lean_object* v_a_00___x40___internal___hyg_609_){
_start:
{
size_t v_ctx_boxed_610_; size_t v_builder_boxed_611_; size_t v_val_boxed_612_; size_t v_store__loc__ptr_boxed_613_; lean_object* v_res_614_; 
v_ctx_boxed_610_ = lean_unbox_usize(v_ctx_605_);
lean_dec(v_ctx_605_);
v_builder_boxed_611_ = lean_unbox_usize(v_builder_606_);
lean_dec(v_builder_606_);
v_val_boxed_612_ = lean_unbox_usize(v_val_607_);
lean_dec(v_val_607_);
v_store__loc__ptr_boxed_613_ = lean_unbox_usize(v_store__loc__ptr_608_);
lean_dec(v_store__loc__ptr_608_);
v_res_614_ = lean_llvm_build_store(v_ctx_boxed_610_, v_builder_boxed_611_, v_val_boxed_612_, v_store__loc__ptr_boxed_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildRet___boxed(lean_object* v_ctx_619_, lean_object* v_builder_620_, lean_object* v_val_621_, lean_object* v_a_00___x40___internal___hyg_622_){
_start:
{
size_t v_ctx_boxed_623_; size_t v_builder_boxed_624_; size_t v_val_boxed_625_; size_t v_res_626_; lean_object* v_r_627_; 
v_ctx_boxed_623_ = lean_unbox_usize(v_ctx_619_);
lean_dec(v_ctx_619_);
v_builder_boxed_624_ = lean_unbox_usize(v_builder_620_);
lean_dec(v_builder_620_);
v_val_boxed_625_ = lean_unbox_usize(v_val_621_);
lean_dec(v_val_621_);
v_res_626_ = lean_llvm_build_ret(v_ctx_boxed_623_, v_builder_boxed_624_, v_val_boxed_625_);
v_r_627_ = lean_box_usize(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildUnreachable___boxed(lean_object* v_ctx_631_, lean_object* v_builder_632_, lean_object* v_a_00___x40___internal___hyg_633_){
_start:
{
size_t v_ctx_boxed_634_; size_t v_builder_boxed_635_; size_t v_res_636_; lean_object* v_r_637_; 
v_ctx_boxed_634_ = lean_unbox_usize(v_ctx_631_);
lean_dec(v_ctx_631_);
v_builder_boxed_635_ = lean_unbox_usize(v_builder_632_);
lean_dec(v_builder_632_);
v_res_636_ = lean_llvm_build_unreachable(v_ctx_boxed_634_, v_builder_boxed_635_);
v_r_637_ = lean_box_usize(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildGEP2___boxed(lean_object* v_ctx_645_, lean_object* v_builder_646_, lean_object* v_ty_647_, lean_object* v_base_648_, lean_object* v_ixs_649_, lean_object* v_name_650_, lean_object* v_a_00___x40___internal___hyg_651_){
_start:
{
size_t v_ctx_boxed_652_; size_t v_builder_boxed_653_; size_t v_ty_boxed_654_; size_t v_base_boxed_655_; size_t v_res_656_; lean_object* v_r_657_; 
v_ctx_boxed_652_ = lean_unbox_usize(v_ctx_645_);
lean_dec(v_ctx_645_);
v_builder_boxed_653_ = lean_unbox_usize(v_builder_646_);
lean_dec(v_builder_646_);
v_ty_boxed_654_ = lean_unbox_usize(v_ty_647_);
lean_dec(v_ty_647_);
v_base_boxed_655_ = lean_unbox_usize(v_base_648_);
lean_dec(v_base_648_);
v_res_656_ = lean_llvm_build_gep2(v_ctx_boxed_652_, v_builder_boxed_653_, v_ty_boxed_654_, v_base_boxed_655_, v_ixs_649_, v_name_650_);
lean_dec_ref(v_ixs_649_);
v_r_657_ = lean_box_usize(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildInBoundsGEP2___boxed(lean_object* v_ctx_665_, lean_object* v_builder_666_, lean_object* v_ty_667_, lean_object* v_base_668_, lean_object* v_ixs_669_, lean_object* v_name_670_, lean_object* v_a_00___x40___internal___hyg_671_){
_start:
{
size_t v_ctx_boxed_672_; size_t v_builder_boxed_673_; size_t v_ty_boxed_674_; size_t v_base_boxed_675_; size_t v_res_676_; lean_object* v_r_677_; 
v_ctx_boxed_672_ = lean_unbox_usize(v_ctx_665_);
lean_dec(v_ctx_665_);
v_builder_boxed_673_ = lean_unbox_usize(v_builder_666_);
lean_dec(v_builder_666_);
v_ty_boxed_674_ = lean_unbox_usize(v_ty_667_);
lean_dec(v_ty_667_);
v_base_boxed_675_ = lean_unbox_usize(v_base_668_);
lean_dec(v_base_668_);
v_res_676_ = lean_llvm_build_inbounds_gep2(v_ctx_boxed_672_, v_builder_boxed_673_, v_ty_boxed_674_, v_base_boxed_675_, v_ixs_669_, v_name_670_);
lean_dec_ref(v_ixs_669_);
v_r_677_ = lean_box_usize(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSext___boxed(lean_object* v_ctx_684_, lean_object* v_builder_685_, lean_object* v_val_686_, lean_object* v_destTy_687_, lean_object* v_name_688_, lean_object* v_a_00___x40___internal___hyg_689_){
_start:
{
size_t v_ctx_boxed_690_; size_t v_builder_boxed_691_; size_t v_val_boxed_692_; size_t v_destTy_boxed_693_; size_t v_res_694_; lean_object* v_r_695_; 
v_ctx_boxed_690_ = lean_unbox_usize(v_ctx_684_);
lean_dec(v_ctx_684_);
v_builder_boxed_691_ = lean_unbox_usize(v_builder_685_);
lean_dec(v_builder_685_);
v_val_boxed_692_ = lean_unbox_usize(v_val_686_);
lean_dec(v_val_686_);
v_destTy_boxed_693_ = lean_unbox_usize(v_destTy_687_);
lean_dec(v_destTy_687_);
v_res_694_ = lean_llvm_build_sext(v_ctx_boxed_690_, v_builder_boxed_691_, v_val_boxed_692_, v_destTy_boxed_693_, v_name_688_);
v_r_695_ = lean_box_usize(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildZext___boxed(lean_object* v_ctx_702_, lean_object* v_builder_703_, lean_object* v_val_704_, lean_object* v_destTy_705_, lean_object* v_name_706_, lean_object* v_a_00___x40___internal___hyg_707_){
_start:
{
size_t v_ctx_boxed_708_; size_t v_builder_boxed_709_; size_t v_val_boxed_710_; size_t v_destTy_boxed_711_; size_t v_res_712_; lean_object* v_r_713_; 
v_ctx_boxed_708_ = lean_unbox_usize(v_ctx_702_);
lean_dec(v_ctx_702_);
v_builder_boxed_709_ = lean_unbox_usize(v_builder_703_);
lean_dec(v_builder_703_);
v_val_boxed_710_ = lean_unbox_usize(v_val_704_);
lean_dec(v_val_704_);
v_destTy_boxed_711_ = lean_unbox_usize(v_destTy_705_);
lean_dec(v_destTy_705_);
v_res_712_ = lean_llvm_build_zext(v_ctx_boxed_708_, v_builder_boxed_709_, v_val_boxed_710_, v_destTy_boxed_711_, v_name_706_);
v_r_713_ = lean_box_usize(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSextOrTrunc___boxed(lean_object* v_ctx_720_, lean_object* v_builder_721_, lean_object* v_val_722_, lean_object* v_destTy_723_, lean_object* v_name_724_, lean_object* v_a_00___x40___internal___hyg_725_){
_start:
{
size_t v_ctx_boxed_726_; size_t v_builder_boxed_727_; size_t v_val_boxed_728_; size_t v_destTy_boxed_729_; size_t v_res_730_; lean_object* v_r_731_; 
v_ctx_boxed_726_ = lean_unbox_usize(v_ctx_720_);
lean_dec(v_ctx_720_);
v_builder_boxed_727_ = lean_unbox_usize(v_builder_721_);
lean_dec(v_builder_721_);
v_val_boxed_728_ = lean_unbox_usize(v_val_722_);
lean_dec(v_val_722_);
v_destTy_boxed_729_ = lean_unbox_usize(v_destTy_723_);
lean_dec(v_destTy_723_);
v_res_730_ = lean_llvm_build_sext_or_trunc(v_ctx_boxed_726_, v_builder_boxed_727_, v_val_boxed_728_, v_destTy_boxed_729_, v_name_724_);
v_r_731_ = lean_box_usize(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSwitch___boxed(lean_object* v_ctx_738_, lean_object* v_builder_739_, lean_object* v_val_740_, lean_object* v_elseBB_741_, lean_object* v_numCasesHint_742_, lean_object* v_a_00___x40___internal___hyg_743_){
_start:
{
size_t v_ctx_boxed_744_; size_t v_builder_boxed_745_; size_t v_val_boxed_746_; size_t v_elseBB_boxed_747_; uint64_t v_numCasesHint_boxed_748_; size_t v_res_749_; lean_object* v_r_750_; 
v_ctx_boxed_744_ = lean_unbox_usize(v_ctx_738_);
lean_dec(v_ctx_738_);
v_builder_boxed_745_ = lean_unbox_usize(v_builder_739_);
lean_dec(v_builder_739_);
v_val_boxed_746_ = lean_unbox_usize(v_val_740_);
lean_dec(v_val_740_);
v_elseBB_boxed_747_ = lean_unbox_usize(v_elseBB_741_);
lean_dec(v_elseBB_741_);
v_numCasesHint_boxed_748_ = lean_unbox_uint64(v_numCasesHint_742_);
lean_dec_ref(v_numCasesHint_742_);
v_res_749_ = lean_llvm_build_switch(v_ctx_boxed_744_, v_builder_boxed_745_, v_val_boxed_746_, v_elseBB_boxed_747_, v_numCasesHint_boxed_748_);
v_r_750_ = lean_box_usize(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildPtrToInt___boxed(lean_object* v_ctx_757_, lean_object* v_builder_758_, lean_object* v_ptr_759_, lean_object* v_destTy_760_, lean_object* v_name_761_, lean_object* v_a_00___x40___internal___hyg_762_){
_start:
{
size_t v_ctx_boxed_763_; size_t v_builder_boxed_764_; size_t v_ptr_boxed_765_; size_t v_destTy_boxed_766_; size_t v_res_767_; lean_object* v_r_768_; 
v_ctx_boxed_763_ = lean_unbox_usize(v_ctx_757_);
lean_dec(v_ctx_757_);
v_builder_boxed_764_ = lean_unbox_usize(v_builder_758_);
lean_dec(v_builder_758_);
v_ptr_boxed_765_ = lean_unbox_usize(v_ptr_759_);
lean_dec(v_ptr_759_);
v_destTy_boxed_766_ = lean_unbox_usize(v_destTy_760_);
lean_dec(v_destTy_760_);
v_res_767_ = lean_llvm_build_ptr_to_int(v_ctx_boxed_763_, v_builder_boxed_764_, v_ptr_boxed_765_, v_destTy_boxed_766_, v_name_761_);
v_r_768_ = lean_box_usize(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildMul___boxed(lean_object* v_ctx_775_, lean_object* v_builder_776_, lean_object* v_x_777_, lean_object* v_y_778_, lean_object* v_name_779_, lean_object* v_a_00___x40___internal___hyg_780_){
_start:
{
size_t v_ctx_boxed_781_; size_t v_builder_boxed_782_; size_t v_x_boxed_783_; size_t v_y_boxed_784_; size_t v_res_785_; lean_object* v_r_786_; 
v_ctx_boxed_781_ = lean_unbox_usize(v_ctx_775_);
lean_dec(v_ctx_775_);
v_builder_boxed_782_ = lean_unbox_usize(v_builder_776_);
lean_dec(v_builder_776_);
v_x_boxed_783_ = lean_unbox_usize(v_x_777_);
lean_dec(v_x_777_);
v_y_boxed_784_ = lean_unbox_usize(v_y_778_);
lean_dec(v_y_778_);
v_res_785_ = lean_llvm_build_mul(v_ctx_boxed_781_, v_builder_boxed_782_, v_x_boxed_783_, v_y_boxed_784_, v_name_779_);
v_r_786_ = lean_box_usize(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAdd___boxed(lean_object* v_ctx_793_, lean_object* v_builder_794_, lean_object* v_x_795_, lean_object* v_y_796_, lean_object* v_name_797_, lean_object* v_a_00___x40___internal___hyg_798_){
_start:
{
size_t v_ctx_boxed_799_; size_t v_builder_boxed_800_; size_t v_x_boxed_801_; size_t v_y_boxed_802_; size_t v_res_803_; lean_object* v_r_804_; 
v_ctx_boxed_799_ = lean_unbox_usize(v_ctx_793_);
lean_dec(v_ctx_793_);
v_builder_boxed_800_ = lean_unbox_usize(v_builder_794_);
lean_dec(v_builder_794_);
v_x_boxed_801_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_y_boxed_802_ = lean_unbox_usize(v_y_796_);
lean_dec(v_y_796_);
v_res_803_ = lean_llvm_build_add(v_ctx_boxed_799_, v_builder_boxed_800_, v_x_boxed_801_, v_y_boxed_802_, v_name_797_);
v_r_804_ = lean_box_usize(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSub___boxed(lean_object* v_ctx_811_, lean_object* v_builder_812_, lean_object* v_x_813_, lean_object* v_y_814_, lean_object* v_name_815_, lean_object* v_a_00___x40___internal___hyg_816_){
_start:
{
size_t v_ctx_boxed_817_; size_t v_builder_boxed_818_; size_t v_x_boxed_819_; size_t v_y_boxed_820_; size_t v_res_821_; lean_object* v_r_822_; 
v_ctx_boxed_817_ = lean_unbox_usize(v_ctx_811_);
lean_dec(v_ctx_811_);
v_builder_boxed_818_ = lean_unbox_usize(v_builder_812_);
lean_dec(v_builder_812_);
v_x_boxed_819_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_y_boxed_820_ = lean_unbox_usize(v_y_814_);
lean_dec(v_y_814_);
v_res_821_ = lean_llvm_build_sub(v_ctx_boxed_817_, v_builder_boxed_818_, v_x_boxed_819_, v_y_boxed_820_, v_name_815_);
v_r_822_ = lean_box_usize(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildNot___boxed(lean_object* v_ctx_828_, lean_object* v_builder_829_, lean_object* v_x_830_, lean_object* v_name_831_, lean_object* v_a_00___x40___internal___hyg_832_){
_start:
{
size_t v_ctx_boxed_833_; size_t v_builder_boxed_834_; size_t v_x_boxed_835_; size_t v_res_836_; lean_object* v_r_837_; 
v_ctx_boxed_833_ = lean_unbox_usize(v_ctx_828_);
lean_dec(v_ctx_828_);
v_builder_boxed_834_ = lean_unbox_usize(v_builder_829_);
lean_dec(v_builder_829_);
v_x_boxed_835_ = lean_unbox_usize(v_x_830_);
lean_dec(v_x_830_);
v_res_836_ = lean_llvm_build_not(v_ctx_boxed_833_, v_builder_boxed_834_, v_x_boxed_835_, v_name_831_);
v_r_837_ = lean_box_usize(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildICmp___boxed(lean_object* v_ctx_845_, lean_object* v_builder_846_, lean_object* v_predicate_847_, lean_object* v_x_848_, lean_object* v_y_849_, lean_object* v_name_850_, lean_object* v_a_00___x40___internal___hyg_851_){
_start:
{
size_t v_ctx_boxed_852_; size_t v_builder_boxed_853_; uint64_t v_predicate_boxed_854_; size_t v_x_boxed_855_; size_t v_y_boxed_856_; size_t v_res_857_; lean_object* v_r_858_; 
v_ctx_boxed_852_ = lean_unbox_usize(v_ctx_845_);
lean_dec(v_ctx_845_);
v_builder_boxed_853_ = lean_unbox_usize(v_builder_846_);
lean_dec(v_builder_846_);
v_predicate_boxed_854_ = lean_unbox_uint64(v_predicate_847_);
lean_dec_ref(v_predicate_847_);
v_x_boxed_855_ = lean_unbox_usize(v_x_848_);
lean_dec(v_x_848_);
v_y_boxed_856_ = lean_unbox_usize(v_y_849_);
lean_dec(v_y_849_);
v_res_857_ = lean_llvm_build_icmp(v_ctx_boxed_852_, v_builder_boxed_853_, v_predicate_boxed_854_, v_x_boxed_855_, v_y_boxed_856_, v_name_850_);
v_r_858_ = lean_box_usize(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addCase___boxed(lean_object* v_ctx_864_, lean_object* v_switch_865_, lean_object* v_onVal_866_, lean_object* v_destBB_867_, lean_object* v_a_00___x40___internal___hyg_868_){
_start:
{
size_t v_ctx_boxed_869_; size_t v_switch_boxed_870_; size_t v_onVal_boxed_871_; size_t v_destBB_boxed_872_; lean_object* v_res_873_; 
v_ctx_boxed_869_ = lean_unbox_usize(v_ctx_864_);
lean_dec(v_ctx_864_);
v_switch_boxed_870_ = lean_unbox_usize(v_switch_865_);
lean_dec(v_switch_865_);
v_onVal_boxed_871_ = lean_unbox_usize(v_onVal_866_);
lean_dec(v_onVal_866_);
v_destBB_boxed_872_ = lean_unbox_usize(v_destBB_867_);
lean_dec(v_destBB_867_);
v_res_873_ = lean_llvm_add_case(v_ctx_boxed_869_, v_switch_boxed_870_, v_onVal_boxed_871_, v_destBB_boxed_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getInsertBlock___boxed(lean_object* v_Context_00___x40_Lean_Compiler_LCNF_LLVMBindings_924321998____hygCtx___hyg_878_, lean_object* v_ctx_879_, lean_object* v_builder_880_, lean_object* v_a_00___x40___internal___hyg_881_){
_start:
{
size_t v_builder_boxed_882_; size_t v_res_883_; lean_object* v_r_884_; 
v_builder_boxed_882_ = lean_unbox_usize(v_builder_880_);
lean_dec(v_builder_880_);
v_res_883_ = lean_llvm_get_insert_block(v_ctx_879_, v_builder_boxed_882_);
v_r_884_ = lean_box_usize(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_LLVM_clearInsertionPosition___boxed(lean_object* v_Context_00___x40_Lean_Compiler_LCNF_LLVMBindings_1700267677____hygCtx___hyg_889_, lean_object* v_ctx_890_, lean_object* v_builder_891_, lean_object* v_a_00___x40___internal___hyg_892_){
_start:
{
size_t v_builder_boxed_893_; lean_object* v_res_894_; 
v_builder_boxed_893_ = lean_unbox_usize(v_builder_891_);
lean_dec(v_builder_891_);
v_res_894_ = lean_llvm_clear_insertion_position(v_ctx_890_, v_builder_boxed_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getBasicBlockParent___boxed(lean_object* v_ctx_898_, lean_object* v_bb_899_, lean_object* v_a_00___x40___internal___hyg_900_){
_start:
{
size_t v_ctx_boxed_901_; size_t v_bb_boxed_902_; size_t v_res_903_; lean_object* v_r_904_; 
v_ctx_boxed_901_ = lean_unbox_usize(v_ctx_898_);
lean_dec(v_ctx_898_);
v_bb_boxed_902_ = lean_unbox_usize(v_bb_899_);
lean_dec(v_bb_899_);
v_res_903_ = lean_llvm_get_basic_block_parent(v_ctx_boxed_901_, v_bb_boxed_902_);
v_r_904_ = lean_box_usize(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT lean_object* l_LLVM_typeOf___boxed(lean_object* v_ctx_908_, lean_object* v_val_909_, lean_object* v_a_00___x40___internal___hyg_910_){
_start:
{
size_t v_ctx_boxed_911_; size_t v_val_boxed_912_; size_t v_res_913_; lean_object* v_r_914_; 
v_ctx_boxed_911_ = lean_unbox_usize(v_ctx_908_);
lean_dec(v_ctx_908_);
v_val_boxed_912_ = lean_unbox_usize(v_val_909_);
lean_dec(v_val_909_);
v_res_913_ = lean_llvm_type_of(v_ctx_boxed_911_, v_val_boxed_912_);
v_r_914_ = lean_box_usize(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt___boxed(lean_object* v_ctx_920_, lean_object* v_intty_921_, lean_object* v_value_922_, lean_object* v_signExtend_923_, lean_object* v_a_00___x40___internal___hyg_924_){
_start:
{
size_t v_ctx_boxed_925_; size_t v_intty_boxed_926_; uint64_t v_value_boxed_927_; uint8_t v_signExtend_boxed_928_; size_t v_res_929_; lean_object* v_r_930_; 
v_ctx_boxed_925_ = lean_unbox_usize(v_ctx_920_);
lean_dec(v_ctx_920_);
v_intty_boxed_926_ = lean_unbox_usize(v_intty_921_);
lean_dec(v_intty_921_);
v_value_boxed_927_ = lean_unbox_uint64(v_value_922_);
lean_dec_ref(v_value_922_);
v_signExtend_boxed_928_ = lean_unbox(v_signExtend_923_);
v_res_929_ = lean_llvm_const_int(v_ctx_boxed_925_, v_intty_boxed_926_, v_value_boxed_927_, v_signExtend_boxed_928_);
v_r_930_ = lean_box_usize(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoString___boxed(lean_object* v_ctx_934_, lean_object* v_mod_935_, lean_object* v_a_00___x40___internal___hyg_936_){
_start:
{
size_t v_ctx_boxed_937_; size_t v_mod_boxed_938_; lean_object* v_res_939_; 
v_ctx_boxed_937_ = lean_unbox_usize(v_ctx_934_);
lean_dec(v_ctx_934_);
v_mod_boxed_938_ = lean_unbox_usize(v_mod_935_);
lean_dec(v_mod_935_);
v_res_939_ = lean_llvm_print_module_to_string(v_ctx_boxed_937_, v_mod_boxed_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoFile___boxed(lean_object* v_ctx_944_, lean_object* v_mod_945_, lean_object* v_file_946_, lean_object* v_a_00___x40___internal___hyg_947_){
_start:
{
size_t v_ctx_boxed_948_; size_t v_mod_boxed_949_; lean_object* v_res_950_; 
v_ctx_boxed_948_ = lean_unbox_usize(v_ctx_944_);
lean_dec(v_ctx_944_);
v_mod_boxed_949_ = lean_unbox_usize(v_mod_945_);
lean_dec(v_mod_945_);
v_res_950_ = lean_llvm_print_module_to_file(v_ctx_boxed_948_, v_mod_boxed_949_, v_file_946_);
lean_dec_ref(v_file_946_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_LLVM_countParams___boxed(lean_object* v_ctx_954_, lean_object* v_fn_955_, lean_object* v_a_00___x40___internal___hyg_956_){
_start:
{
size_t v_ctx_boxed_957_; size_t v_fn_boxed_958_; uint64_t v_res_959_; lean_object* v_r_960_; 
v_ctx_boxed_957_ = lean_unbox_usize(v_ctx_954_);
lean_dec(v_ctx_954_);
v_fn_boxed_958_ = lean_unbox_usize(v_fn_955_);
lean_dec(v_fn_955_);
v_res_959_ = llvm_count_params(v_ctx_boxed_957_, v_fn_boxed_958_);
v_r_960_ = lean_box_uint64(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getParam___boxed(lean_object* v_ctx_965_, lean_object* v_fn_966_, lean_object* v_ix_967_, lean_object* v_a_00___x40___internal___hyg_968_){
_start:
{
size_t v_ctx_boxed_969_; size_t v_fn_boxed_970_; uint64_t v_ix_boxed_971_; size_t v_res_972_; lean_object* v_r_973_; 
v_ctx_boxed_969_ = lean_unbox_usize(v_ctx_965_);
lean_dec(v_ctx_965_);
v_fn_boxed_970_ = lean_unbox_usize(v_fn_966_);
lean_dec(v_fn_966_);
v_ix_boxed_971_ = lean_unbox_uint64(v_ix_967_);
lean_dec_ref(v_ix_967_);
v_res_972_ = llvm_get_param(v_ctx_boxed_969_, v_fn_boxed_970_, v_ix_boxed_971_);
v_r_973_ = lean_box_usize(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createMemoryBufferWithContentsOfFile___boxed(lean_object* v_ctx_977_, lean_object* v_path_978_, lean_object* v_a_00___x40___internal___hyg_979_){
_start:
{
size_t v_ctx_boxed_980_; size_t v_res_981_; lean_object* v_r_982_; 
v_ctx_boxed_980_ = lean_unbox_usize(v_ctx_977_);
lean_dec(v_ctx_977_);
v_res_981_ = lean_llvm_create_memory_buffer_with_contents_of_file(v_ctx_boxed_980_, v_path_978_);
lean_dec_ref(v_path_978_);
v_r_982_ = lean_box_usize(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l_LLVM_parseBitcode___boxed(lean_object* v_ctx_986_, lean_object* v_membuf_987_, lean_object* v_a_00___x40___internal___hyg_988_){
_start:
{
size_t v_ctx_boxed_989_; size_t v_membuf_boxed_990_; size_t v_res_991_; lean_object* v_r_992_; 
v_ctx_boxed_989_ = lean_unbox_usize(v_ctx_986_);
lean_dec(v_ctx_986_);
v_membuf_boxed_990_ = lean_unbox_usize(v_membuf_987_);
lean_dec(v_membuf_987_);
v_res_991_ = lean_llvm_parse_bitcode(v_ctx_boxed_989_, v_membuf_boxed_990_);
v_r_992_ = lean_box_usize(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT lean_object* l_LLVM_linkModules___boxed(lean_object* v_ctx_997_, lean_object* v_dest_998_, lean_object* v_src_999_, lean_object* v_a_00___x40___internal___hyg_1000_){
_start:
{
size_t v_ctx_boxed_1001_; size_t v_dest_boxed_1002_; size_t v_src_boxed_1003_; lean_object* v_res_1004_; 
v_ctx_boxed_1001_ = lean_unbox_usize(v_ctx_997_);
lean_dec(v_ctx_997_);
v_dest_boxed_1002_ = lean_unbox_usize(v_dest_998_);
lean_dec(v_dest_998_);
v_src_boxed_1003_ = lean_unbox_usize(v_src_999_);
lean_dec(v_src_999_);
v_res_1004_ = lean_llvm_link_modules(v_ctx_boxed_1001_, v_dest_boxed_1002_, v_src_boxed_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getDefaultTargetTriple___boxed(lean_object* v_a_00___x40___internal___hyg_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = lean_llvm_get_default_target_triple();
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getTargetFromTriple___boxed(lean_object* v_ctx_1011_, lean_object* v_triple_1012_, lean_object* v_a_00___x40___internal___hyg_1013_){
_start:
{
size_t v_ctx_boxed_1014_; size_t v_res_1015_; lean_object* v_r_1016_; 
v_ctx_boxed_1014_ = lean_unbox_usize(v_ctx_1011_);
lean_dec(v_ctx_1011_);
v_res_1015_ = lean_llvm_get_target_from_triple(v_ctx_boxed_1014_, v_triple_1012_);
lean_dec_ref(v_triple_1012_);
v_r_1016_ = lean_box_usize(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createTargetMachine___boxed(lean_object* v_ctx_1023_, lean_object* v_target_1024_, lean_object* v_tripleStr_1025_, lean_object* v_cpu_1026_, lean_object* v_features_1027_, lean_object* v_a_00___x40___internal___hyg_1028_){
_start:
{
size_t v_ctx_boxed_1029_; size_t v_target_boxed_1030_; size_t v_res_1031_; lean_object* v_r_1032_; 
v_ctx_boxed_1029_ = lean_unbox_usize(v_ctx_1023_);
lean_dec(v_ctx_1023_);
v_target_boxed_1030_ = lean_unbox_usize(v_target_1024_);
lean_dec(v_target_1024_);
v_res_1031_ = lean_llvm_create_target_machine(v_ctx_boxed_1029_, v_target_boxed_1030_, v_tripleStr_1025_, v_cpu_1026_, v_features_1027_);
lean_dec_ref(v_features_1027_);
lean_dec_ref(v_cpu_1026_);
lean_dec_ref(v_tripleStr_1025_);
v_r_1032_ = lean_box_usize(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l_LLVM_targetMachineEmitToFile___boxed(lean_object* v_ctx_1039_, lean_object* v_targetMachine_1040_, lean_object* v_module_1041_, lean_object* v_filepath_1042_, lean_object* v_codegenType_1043_, lean_object* v_a_00___x40___internal___hyg_1044_){
_start:
{
size_t v_ctx_boxed_1045_; size_t v_targetMachine_boxed_1046_; size_t v_module_boxed_1047_; uint64_t v_codegenType_boxed_1048_; lean_object* v_res_1049_; 
v_ctx_boxed_1045_ = lean_unbox_usize(v_ctx_1039_);
lean_dec(v_ctx_1039_);
v_targetMachine_boxed_1046_ = lean_unbox_usize(v_targetMachine_1040_);
lean_dec(v_targetMachine_1040_);
v_module_boxed_1047_ = lean_unbox_usize(v_module_1041_);
lean_dec(v_module_1041_);
v_codegenType_boxed_1048_ = lean_unbox_uint64(v_codegenType_1043_);
lean_dec_ref(v_codegenType_1043_);
v_res_1049_ = lean_llvm_target_machine_emit_to_file(v_ctx_boxed_1045_, v_targetMachine_boxed_1046_, v_module_boxed_1047_, v_filepath_1042_, v_codegenType_boxed_1048_);
lean_dec_ref(v_filepath_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeTargetMachine___boxed(lean_object* v_ctx_1053_, lean_object* v_tm_1054_, lean_object* v_a_00___x40___internal___hyg_1055_){
_start:
{
size_t v_ctx_boxed_1056_; size_t v_tm_boxed_1057_; lean_object* v_res_1058_; 
v_ctx_boxed_1056_ = lean_unbox_usize(v_ctx_1053_);
lean_dec(v_ctx_1053_);
v_tm_boxed_1057_ = lean_unbox_usize(v_tm_1054_);
lean_dec(v_tm_1054_);
v_res_1058_ = lean_llvm_dispose_target_machine(v_ctx_boxed_1056_, v_tm_boxed_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeModule___boxed(lean_object* v_ctx_1062_, lean_object* v_m_1063_, lean_object* v_a_00___x40___internal___hyg_1064_){
_start:
{
size_t v_ctx_boxed_1065_; size_t v_m_boxed_1066_; lean_object* v_res_1067_; 
v_ctx_boxed_1065_ = lean_unbox_usize(v_ctx_1062_);
lean_dec(v_ctx_1062_);
v_m_boxed_1066_ = lean_unbox_usize(v_m_1063_);
lean_dec(v_m_1063_);
v_res_1067_ = lean_llvm_dispose_module(v_ctx_boxed_1065_, v_m_boxed_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_LLVM_verifyModule___boxed(lean_object* v_ctx_1071_, lean_object* v_m_1072_, lean_object* v_a_00___x40___internal___hyg_1073_){
_start:
{
size_t v_ctx_boxed_1074_; size_t v_m_boxed_1075_; lean_object* v_res_1076_; 
v_ctx_boxed_1074_ = lean_unbox_usize(v_ctx_1071_);
lean_dec(v_ctx_1071_);
v_m_boxed_1075_ = lean_unbox_usize(v_m_1072_);
lean_dec(v_m_1072_);
v_res_1076_ = lean_llvm_verify_module(v_ctx_boxed_1074_, v_m_boxed_1075_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createStringAttribute___boxed(lean_object* v_ctx_1081_, lean_object* v_key_1082_, lean_object* v_value_1083_, lean_object* v_a_00___x40___internal___hyg_1084_){
_start:
{
size_t v_ctx_boxed_1085_; size_t v_res_1086_; lean_object* v_r_1087_; 
v_ctx_boxed_1085_ = lean_unbox_usize(v_ctx_1081_);
lean_dec(v_ctx_1081_);
v_res_1086_ = lean_llvm_create_string_attribute(v_ctx_boxed_1085_, v_key_1082_, v_value_1083_);
v_r_1087_ = lean_box_usize(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addAttributeAtIndex___boxed(lean_object* v_ctx_1093_, lean_object* v_fn_1094_, lean_object* v_idx_1095_, lean_object* v_attr_1096_, lean_object* v_a_00___x40___internal___hyg_1097_){
_start:
{
size_t v_ctx_boxed_1098_; size_t v_fn_boxed_1099_; uint64_t v_idx_boxed_1100_; size_t v_attr_boxed_1101_; lean_object* v_res_1102_; 
v_ctx_boxed_1098_ = lean_unbox_usize(v_ctx_1093_);
lean_dec(v_ctx_1093_);
v_fn_boxed_1099_ = lean_unbox_usize(v_fn_1094_);
lean_dec(v_fn_1094_);
v_idx_boxed_1100_ = lean_unbox_uint64(v_idx_1095_);
lean_dec_ref(v_idx_1095_);
v_attr_boxed_1101_ = lean_unbox_usize(v_attr_1096_);
lean_dec(v_attr_1096_);
v_res_1102_ = lean_llvm_add_attribute_at_index(v_ctx_boxed_1098_, v_fn_boxed_1099_, v_idx_boxed_1100_, v_attr_boxed_1101_);
return v_res_1102_;
}
}
static uint64_t _init_l_LLVM_Visibility_default(void){
_start:
{
uint64_t v___x_1103_; 
v___x_1103_ = 0ULL;
return v___x_1103_;
}
}
static uint64_t _init_l_LLVM_Visibility_hidden(void){
_start:
{
uint64_t v___x_1104_; 
v___x_1104_ = 1ULL;
return v___x_1104_;
}
}
static uint64_t _init_l_LLVM_Visibility_protected(void){
_start:
{
uint64_t v___x_1105_; 
v___x_1105_ = 2ULL;
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setVisibility___boxed(lean_object* v_ctx_1110_, lean_object* v_value_1111_, lean_object* v_visibility_1112_, lean_object* v_a_00___x40___internal___hyg_1113_){
_start:
{
size_t v_ctx_boxed_1114_; size_t v_value_boxed_1115_; uint64_t v_visibility_boxed_1116_; lean_object* v_res_1117_; 
v_ctx_boxed_1114_ = lean_unbox_usize(v_ctx_1110_);
lean_dec(v_ctx_1110_);
v_value_boxed_1115_ = lean_unbox_usize(v_value_1111_);
lean_dec(v_value_1111_);
v_visibility_boxed_1116_ = lean_unbox_uint64(v_visibility_1112_);
lean_dec_ref(v_visibility_1112_);
v_res_1117_ = lean_llvm_set_visibility(v_ctx_boxed_1114_, v_value_boxed_1115_, v_visibility_boxed_1116_);
return v_res_1117_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_default(void){
_start:
{
uint64_t v___x_1118_; 
v___x_1118_ = 0ULL;
return v___x_1118_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_import(void){
_start:
{
uint64_t v___x_1119_; 
v___x_1119_ = 1ULL;
return v___x_1119_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_export(void){
_start:
{
uint64_t v___x_1120_; 
v___x_1120_ = 2ULL;
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setDLLStorageClass___boxed(lean_object* v_ctx_1125_, lean_object* v_value_1126_, lean_object* v_dllStorageClass_1127_, lean_object* v_a_00___x40___internal___hyg_1128_){
_start:
{
size_t v_ctx_boxed_1129_; size_t v_value_boxed_1130_; uint64_t v_dllStorageClass_boxed_1131_; lean_object* v_res_1132_; 
v_ctx_boxed_1129_ = lean_unbox_usize(v_ctx_1125_);
lean_dec(v_ctx_1125_);
v_value_boxed_1130_ = lean_unbox_usize(v_value_1126_);
lean_dec(v_value_1126_);
v_dllStorageClass_boxed_1131_ = lean_unbox_uint64(v_dllStorageClass_1127_);
lean_dec_ref(v_dllStorageClass_1127_);
v_res_1132_ = lean_llvm_set_dll_storage_class(v_ctx_boxed_1129_, v_value_boxed_1130_, v_dllStorageClass_boxed_1131_);
return v_res_1132_;
}
}
static uint64_t _init_l_LLVM_Linkage_external(void){
_start:
{
uint64_t v___x_1133_; 
v___x_1133_ = 0ULL;
return v___x_1133_;
}
}
static uint64_t _init_l_LLVM_Linkage_availableExternally(void){
_start:
{
uint64_t v___x_1134_; 
v___x_1134_ = 1ULL;
return v___x_1134_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceAny(void){
_start:
{
uint64_t v___x_1135_; 
v___x_1135_ = 2ULL;
return v___x_1135_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceODR(void){
_start:
{
uint64_t v___x_1136_; 
v___x_1136_ = 3ULL;
return v___x_1136_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceODRAutoHide(void){
_start:
{
uint64_t v___x_1137_; 
v___x_1137_ = 4ULL;
return v___x_1137_;
}
}
static uint64_t _init_l_LLVM_Linkage_weakAny(void){
_start:
{
uint64_t v___x_1138_; 
v___x_1138_ = 5ULL;
return v___x_1138_;
}
}
static uint64_t _init_l_LLVM_Linkage_weakODR(void){
_start:
{
uint64_t v___x_1139_; 
v___x_1139_ = 6ULL;
return v___x_1139_;
}
}
static uint64_t _init_l_LLVM_Linkage_appending(void){
_start:
{
uint64_t v___x_1140_; 
v___x_1140_ = 7ULL;
return v___x_1140_;
}
}
static uint64_t _init_l_LLVM_Linkage_internal(void){
_start:
{
uint64_t v___x_1141_; 
v___x_1141_ = 8ULL;
return v___x_1141_;
}
}
static uint64_t _init_l_LLVM_Linkage_private(void){
_start:
{
uint64_t v___x_1142_; 
v___x_1142_ = 9ULL;
return v___x_1142_;
}
}
static uint64_t _init_l_LLVM_Linkage_dllImport(void){
_start:
{
uint64_t v___x_1143_; 
v___x_1143_ = 10ULL;
return v___x_1143_;
}
}
static uint64_t _init_l_LLVM_Linkage_dllExport(void){
_start:
{
uint64_t v___x_1144_; 
v___x_1144_ = 11ULL;
return v___x_1144_;
}
}
static uint64_t _init_l_LLVM_Linkage_externalWeak(void){
_start:
{
uint64_t v___x_1145_; 
v___x_1145_ = 12ULL;
return v___x_1145_;
}
}
static uint64_t _init_l_LLVM_Linkage_ghost(void){
_start:
{
uint64_t v___x_1146_; 
v___x_1146_ = 13ULL;
return v___x_1146_;
}
}
static uint64_t _init_l_LLVM_Linkage_common(void){
_start:
{
uint64_t v___x_1147_; 
v___x_1147_ = 14ULL;
return v___x_1147_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkerPrivate(void){
_start:
{
uint64_t v___x_1148_; 
v___x_1148_ = 15ULL;
return v___x_1148_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkerPrivateWeak(void){
_start:
{
uint64_t v___x_1149_; 
v___x_1149_ = 16ULL;
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setLinkage___boxed(lean_object* v_ctx_1154_, lean_object* v_value_1155_, lean_object* v_linkage_1156_, lean_object* v_a_00___x40___internal___hyg_1157_){
_start:
{
size_t v_ctx_boxed_1158_; size_t v_value_boxed_1159_; uint64_t v_linkage_boxed_1160_; lean_object* v_res_1161_; 
v_ctx_boxed_1158_ = lean_unbox_usize(v_ctx_1154_);
lean_dec(v_ctx_1154_);
v_value_boxed_1159_ = lean_unbox_usize(v_value_1155_);
lean_dec(v_value_1155_);
v_linkage_boxed_1160_ = lean_unbox_uint64(v_linkage_1156_);
lean_dec_ref(v_linkage_1156_);
v_res_1161_ = lean_llvm_set_linkage(v_ctx_boxed_1158_, v_value_boxed_1159_, v_linkage_boxed_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT size_t l_LLVM_i1Type(size_t v_ctx_1162_){
_start:
{
uint64_t v___x_1164_; size_t v___x_1165_; 
v___x_1164_ = 1ULL;
v___x_1165_ = lean_llvm_int_type_in_context(v_ctx_1162_, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i1Type___boxed(lean_object* v_ctx_1166_, lean_object* v_a_1167_){
_start:
{
size_t v_ctx_boxed_1168_; size_t v_res_1169_; lean_object* v_r_1170_; 
v_ctx_boxed_1168_ = lean_unbox_usize(v_ctx_1166_);
lean_dec(v_ctx_1166_);
v_res_1169_ = l_LLVM_i1Type(v_ctx_boxed_1168_);
v_r_1170_ = lean_box_usize(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT size_t l_LLVM_i8Type(size_t v_ctx_1171_){
_start:
{
uint64_t v___x_1173_; size_t v___x_1174_; 
v___x_1173_ = 8ULL;
v___x_1174_ = lean_llvm_int_type_in_context(v_ctx_1171_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8Type___boxed(lean_object* v_ctx_1175_, lean_object* v_a_1176_){
_start:
{
size_t v_ctx_boxed_1177_; size_t v_res_1178_; lean_object* v_r_1179_; 
v_ctx_boxed_1177_ = lean_unbox_usize(v_ctx_1175_);
lean_dec(v_ctx_1175_);
v_res_1178_ = l_LLVM_i8Type(v_ctx_boxed_1177_);
v_r_1179_ = lean_box_usize(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT size_t l_LLVM_i16Type(size_t v_ctx_1180_){
_start:
{
uint64_t v___x_1182_; size_t v___x_1183_; 
v___x_1182_ = 16ULL;
v___x_1183_ = lean_llvm_int_type_in_context(v_ctx_1180_, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i16Type___boxed(lean_object* v_ctx_1184_, lean_object* v_a_1185_){
_start:
{
size_t v_ctx_boxed_1186_; size_t v_res_1187_; lean_object* v_r_1188_; 
v_ctx_boxed_1186_ = lean_unbox_usize(v_ctx_1184_);
lean_dec(v_ctx_1184_);
v_res_1187_ = l_LLVM_i16Type(v_ctx_boxed_1186_);
v_r_1188_ = lean_box_usize(v_res_1187_);
return v_r_1188_;
}
}
LEAN_EXPORT size_t l_LLVM_i32Type(size_t v_ctx_1189_){
_start:
{
uint64_t v___x_1191_; size_t v___x_1192_; 
v___x_1191_ = 32ULL;
v___x_1192_ = lean_llvm_int_type_in_context(v_ctx_1189_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i32Type___boxed(lean_object* v_ctx_1193_, lean_object* v_a_1194_){
_start:
{
size_t v_ctx_boxed_1195_; size_t v_res_1196_; lean_object* v_r_1197_; 
v_ctx_boxed_1195_ = lean_unbox_usize(v_ctx_1193_);
lean_dec(v_ctx_1193_);
v_res_1196_ = l_LLVM_i32Type(v_ctx_boxed_1195_);
v_r_1197_ = lean_box_usize(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT size_t l_LLVM_i64Type(size_t v_ctx_1198_){
_start:
{
uint64_t v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = 64ULL;
v___x_1201_ = lean_llvm_int_type_in_context(v_ctx_1198_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i64Type___boxed(lean_object* v_ctx_1202_, lean_object* v_a_1203_){
_start:
{
size_t v_ctx_boxed_1204_; size_t v_res_1205_; lean_object* v_r_1206_; 
v_ctx_boxed_1204_ = lean_unbox_usize(v_ctx_1202_);
lean_dec(v_ctx_1202_);
v_res_1205_ = l_LLVM_i64Type(v_ctx_boxed_1204_);
v_r_1206_ = lean_box_usize(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT size_t l_LLVM_voidPtrType(size_t v_ctx_1207_){
_start:
{
uint64_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; 
v___x_1209_ = 8ULL;
v___x_1210_ = lean_llvm_int_type_in_context(v_ctx_1207_, v___x_1209_);
v___x_1211_ = lean_llvm_pointer_type(v_ctx_1207_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_LLVM_voidPtrType___boxed(lean_object* v_ctx_1212_, lean_object* v_a_1213_){
_start:
{
size_t v_ctx_boxed_1214_; size_t v_res_1215_; lean_object* v_r_1216_; 
v_ctx_boxed_1214_ = lean_unbox_usize(v_ctx_1212_);
lean_dec(v_ctx_1212_);
v_res_1215_ = l_LLVM_voidPtrType(v_ctx_boxed_1214_);
v_r_1216_ = lean_box_usize(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT size_t l_LLVM_i8PtrType(size_t v_ctx_1217_){
_start:
{
size_t v___x_1219_; 
v___x_1219_ = l_LLVM_voidPtrType(v_ctx_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8PtrType___boxed(lean_object* v_ctx_1220_, lean_object* v_a_1221_){
_start:
{
size_t v_ctx_boxed_1222_; size_t v_res_1223_; lean_object* v_r_1224_; 
v_ctx_boxed_1222_ = lean_unbox_usize(v_ctx_1220_);
lean_dec(v_ctx_1220_);
v_res_1223_ = l_LLVM_i8PtrType(v_ctx_boxed_1222_);
v_r_1224_ = lean_box_usize(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT size_t l_LLVM_constTrue(size_t v_ctx_1225_){
_start:
{
size_t v___x_1227_; uint64_t v___x_1228_; uint8_t v___x_1229_; size_t v___x_1230_; 
v___x_1227_ = l_LLVM_i1Type(v_ctx_1225_);
v___x_1228_ = 1ULL;
v___x_1229_ = 0;
v___x_1230_ = lean_llvm_const_int(v_ctx_1225_, v___x_1227_, v___x_1228_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constTrue___boxed(lean_object* v_ctx_1231_, lean_object* v_a_1232_){
_start:
{
size_t v_ctx_boxed_1233_; size_t v_res_1234_; lean_object* v_r_1235_; 
v_ctx_boxed_1233_ = lean_unbox_usize(v_ctx_1231_);
lean_dec(v_ctx_1231_);
v_res_1234_ = l_LLVM_constTrue(v_ctx_boxed_1233_);
v_r_1235_ = lean_box_usize(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT size_t l_LLVM_constFalse(size_t v_ctx_1236_){
_start:
{
size_t v___x_1238_; uint64_t v___x_1239_; uint8_t v___x_1240_; size_t v___x_1241_; 
v___x_1238_ = l_LLVM_i1Type(v_ctx_1236_);
v___x_1239_ = 0ULL;
v___x_1240_ = 0;
v___x_1241_ = lean_llvm_const_int(v_ctx_1236_, v___x_1238_, v___x_1239_, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constFalse___boxed(lean_object* v_ctx_1242_, lean_object* v_a_1243_){
_start:
{
size_t v_ctx_boxed_1244_; size_t v_res_1245_; lean_object* v_r_1246_; 
v_ctx_boxed_1244_ = lean_unbox_usize(v_ctx_1242_);
lean_dec(v_ctx_1242_);
v_res_1245_ = l_LLVM_constFalse(v_ctx_boxed_1244_);
v_r_1246_ = lean_box_usize(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt_x27(size_t v_ctx_1247_, uint64_t v_width_1248_, uint64_t v_value_1249_, uint8_t v_signExtend_1250_){
_start:
{
size_t v___x_1252_; size_t v___x_1253_; 
v___x_1252_ = lean_llvm_int_type_in_context(v_ctx_1247_, v_width_1248_);
v___x_1253_ = lean_llvm_const_int(v_ctx_1247_, v___x_1252_, v_value_1249_, v_signExtend_1250_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt_x27___boxed(lean_object* v_ctx_1254_, lean_object* v_width_1255_, lean_object* v_value_1256_, lean_object* v_signExtend_1257_, lean_object* v_a_1258_){
_start:
{
size_t v_ctx_boxed_1259_; uint64_t v_width_boxed_1260_; uint64_t v_value_boxed_1261_; uint8_t v_signExtend_boxed_1262_; size_t v_res_1263_; lean_object* v_r_1264_; 
v_ctx_boxed_1259_ = lean_unbox_usize(v_ctx_1254_);
lean_dec(v_ctx_1254_);
v_width_boxed_1260_ = lean_unbox_uint64(v_width_1255_);
lean_dec_ref(v_width_1255_);
v_value_boxed_1261_ = lean_unbox_uint64(v_value_1256_);
lean_dec_ref(v_value_1256_);
v_signExtend_boxed_1262_ = lean_unbox(v_signExtend_1257_);
v_res_1263_ = l_LLVM_constInt_x27(v_ctx_boxed_1259_, v_width_boxed_1260_, v_value_boxed_1261_, v_signExtend_boxed_1262_);
v_r_1264_ = lean_box_usize(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt1(size_t v_ctx_1265_, uint64_t v_value_1266_, uint8_t v_signExtend_1267_){
_start:
{
uint64_t v___x_1269_; size_t v___x_1270_; 
v___x_1269_ = 1ULL;
v___x_1270_ = l_LLVM_constInt_x27(v_ctx_1265_, v___x_1269_, v_value_1266_, v_signExtend_1267_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt1___boxed(lean_object* v_ctx_1271_, lean_object* v_value_1272_, lean_object* v_signExtend_1273_, lean_object* v_a_1274_){
_start:
{
size_t v_ctx_boxed_1275_; uint64_t v_value_boxed_1276_; uint8_t v_signExtend_boxed_1277_; size_t v_res_1278_; lean_object* v_r_1279_; 
v_ctx_boxed_1275_ = lean_unbox_usize(v_ctx_1271_);
lean_dec(v_ctx_1271_);
v_value_boxed_1276_ = lean_unbox_uint64(v_value_1272_);
lean_dec_ref(v_value_1272_);
v_signExtend_boxed_1277_ = lean_unbox(v_signExtend_1273_);
v_res_1278_ = l_LLVM_constInt1(v_ctx_boxed_1275_, v_value_boxed_1276_, v_signExtend_boxed_1277_);
v_r_1279_ = lean_box_usize(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt8(size_t v_ctx_1280_, uint64_t v_value_1281_, uint8_t v_signExtend_1282_){
_start:
{
uint64_t v___x_1284_; size_t v___x_1285_; 
v___x_1284_ = 8ULL;
v___x_1285_ = l_LLVM_constInt_x27(v_ctx_1280_, v___x_1284_, v_value_1281_, v_signExtend_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt8___boxed(lean_object* v_ctx_1286_, lean_object* v_value_1287_, lean_object* v_signExtend_1288_, lean_object* v_a_1289_){
_start:
{
size_t v_ctx_boxed_1290_; uint64_t v_value_boxed_1291_; uint8_t v_signExtend_boxed_1292_; size_t v_res_1293_; lean_object* v_r_1294_; 
v_ctx_boxed_1290_ = lean_unbox_usize(v_ctx_1286_);
lean_dec(v_ctx_1286_);
v_value_boxed_1291_ = lean_unbox_uint64(v_value_1287_);
lean_dec_ref(v_value_1287_);
v_signExtend_boxed_1292_ = lean_unbox(v_signExtend_1288_);
v_res_1293_ = l_LLVM_constInt8(v_ctx_boxed_1290_, v_value_boxed_1291_, v_signExtend_boxed_1292_);
v_r_1294_ = lean_box_usize(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt32(size_t v_ctx_1295_, uint64_t v_value_1296_, uint8_t v_signExtend_1297_){
_start:
{
uint64_t v___x_1299_; size_t v___x_1300_; 
v___x_1299_ = 32ULL;
v___x_1300_ = l_LLVM_constInt_x27(v_ctx_1295_, v___x_1299_, v_value_1296_, v_signExtend_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt32___boxed(lean_object* v_ctx_1301_, lean_object* v_value_1302_, lean_object* v_signExtend_1303_, lean_object* v_a_1304_){
_start:
{
size_t v_ctx_boxed_1305_; uint64_t v_value_boxed_1306_; uint8_t v_signExtend_boxed_1307_; size_t v_res_1308_; lean_object* v_r_1309_; 
v_ctx_boxed_1305_ = lean_unbox_usize(v_ctx_1301_);
lean_dec(v_ctx_1301_);
v_value_boxed_1306_ = lean_unbox_uint64(v_value_1302_);
lean_dec_ref(v_value_1302_);
v_signExtend_boxed_1307_ = lean_unbox(v_signExtend_1303_);
v_res_1308_ = l_LLVM_constInt32(v_ctx_boxed_1305_, v_value_boxed_1306_, v_signExtend_boxed_1307_);
v_r_1309_ = lean_box_usize(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt64(size_t v_ctx_1310_, uint64_t v_value_1311_, uint8_t v_signExtend_1312_){
_start:
{
uint64_t v___x_1314_; size_t v___x_1315_; 
v___x_1314_ = 64ULL;
v___x_1315_ = l_LLVM_constInt_x27(v_ctx_1310_, v___x_1314_, v_value_1311_, v_signExtend_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt64___boxed(lean_object* v_ctx_1316_, lean_object* v_value_1317_, lean_object* v_signExtend_1318_, lean_object* v_a_1319_){
_start:
{
size_t v_ctx_boxed_1320_; uint64_t v_value_boxed_1321_; uint8_t v_signExtend_boxed_1322_; size_t v_res_1323_; lean_object* v_r_1324_; 
v_ctx_boxed_1320_ = lean_unbox_usize(v_ctx_1316_);
lean_dec(v_ctx_1316_);
v_value_boxed_1321_ = lean_unbox_uint64(v_value_1317_);
lean_dec_ref(v_value_1317_);
v_signExtend_boxed_1322_ = lean_unbox(v_signExtend_1318_);
v_res_1323_ = l_LLVM_constInt64(v_ctx_boxed_1320_, v_value_boxed_1321_, v_signExtend_boxed_1322_);
v_r_1324_ = lean_box_usize(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT size_t l_LLVM_constIntSizeT(size_t v_ctx_1325_, uint64_t v_value_1326_, uint8_t v_signExtend_1327_){
_start:
{
uint64_t v___x_1329_; size_t v___x_1330_; 
v___x_1329_ = 64ULL;
v___x_1330_ = l_LLVM_constInt_x27(v_ctx_1325_, v___x_1329_, v_value_1326_, v_signExtend_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntSizeT___boxed(lean_object* v_ctx_1331_, lean_object* v_value_1332_, lean_object* v_signExtend_1333_, lean_object* v_a_1334_){
_start:
{
size_t v_ctx_boxed_1335_; uint64_t v_value_boxed_1336_; uint8_t v_signExtend_boxed_1337_; size_t v_res_1338_; lean_object* v_r_1339_; 
v_ctx_boxed_1335_ = lean_unbox_usize(v_ctx_1331_);
lean_dec(v_ctx_1331_);
v_value_boxed_1336_ = lean_unbox_uint64(v_value_1332_);
lean_dec_ref(v_value_1332_);
v_signExtend_boxed_1337_ = lean_unbox(v_signExtend_1333_);
v_res_1338_ = l_LLVM_constIntSizeT(v_ctx_boxed_1335_, v_value_boxed_1336_, v_signExtend_boxed_1337_);
v_r_1339_ = lean_box_usize(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT size_t l_LLVM_constIntUnsigned(size_t v_ctx_1340_, uint64_t v_value_1341_, uint8_t v_signExtend_1342_){
_start:
{
uint64_t v___x_1344_; size_t v___x_1345_; 
v___x_1344_ = 32ULL;
v___x_1345_ = l_LLVM_constInt_x27(v_ctx_1340_, v___x_1344_, v_value_1341_, v_signExtend_1342_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned___boxed(lean_object* v_ctx_1346_, lean_object* v_value_1347_, lean_object* v_signExtend_1348_, lean_object* v_a_1349_){
_start:
{
size_t v_ctx_boxed_1350_; uint64_t v_value_boxed_1351_; uint8_t v_signExtend_boxed_1352_; size_t v_res_1353_; lean_object* v_r_1354_; 
v_ctx_boxed_1350_ = lean_unbox_usize(v_ctx_1346_);
lean_dec(v_ctx_1346_);
v_value_boxed_1351_ = lean_unbox_uint64(v_value_1347_);
lean_dec_ref(v_value_1347_);
v_signExtend_boxed_1352_ = lean_unbox(v_signExtend_1348_);
v_res_1353_ = l_LLVM_constIntUnsigned(v_ctx_boxed_1350_, v_value_boxed_1351_, v_signExtend_boxed_1352_);
v_r_1354_ = lean_box_usize(v_res_1353_);
return v_r_1354_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_LLVMBindings(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LLVM_CodegenFileType_AssemblyFile = _init_l_LLVM_CodegenFileType_AssemblyFile();
l_LLVM_CodegenFileType_ObjectFile = _init_l_LLVM_CodegenFileType_ObjectFile();
l_LLVM_IntPredicate_EQ = _init_l_LLVM_IntPredicate_EQ();
l_LLVM_IntPredicate_NE = _init_l_LLVM_IntPredicate_NE();
l_LLVM_IntPredicate_UGT = _init_l_LLVM_IntPredicate_UGT();
l_LLVM_AttributeIndex_AttributeReturnIndex = _init_l_LLVM_AttributeIndex_AttributeReturnIndex();
l_LLVM_AttributeIndex_AttributeFunctionIndex = _init_l_LLVM_AttributeIndex_AttributeFunctionIndex();
l_LLVM_TailCallKind_none = _init_l_LLVM_TailCallKind_none();
l_LLVM_TailCallKind_tail = _init_l_LLVM_TailCallKind_tail();
l_LLVM_TailCallKind_mustTail = _init_l_LLVM_TailCallKind_mustTail();
l_LLVM_TailCallKind_noTail = _init_l_LLVM_TailCallKind_noTail();
l_LLVM_Visibility_default = _init_l_LLVM_Visibility_default();
l_LLVM_Visibility_hidden = _init_l_LLVM_Visibility_hidden();
l_LLVM_Visibility_protected = _init_l_LLVM_Visibility_protected();
l_LLVM_DLLStorageClass_default = _init_l_LLVM_DLLStorageClass_default();
l_LLVM_DLLStorageClass_import = _init_l_LLVM_DLLStorageClass_import();
l_LLVM_DLLStorageClass_export = _init_l_LLVM_DLLStorageClass_export();
l_LLVM_Linkage_external = _init_l_LLVM_Linkage_external();
l_LLVM_Linkage_availableExternally = _init_l_LLVM_Linkage_availableExternally();
l_LLVM_Linkage_linkOnceAny = _init_l_LLVM_Linkage_linkOnceAny();
l_LLVM_Linkage_linkOnceODR = _init_l_LLVM_Linkage_linkOnceODR();
l_LLVM_Linkage_linkOnceODRAutoHide = _init_l_LLVM_Linkage_linkOnceODRAutoHide();
l_LLVM_Linkage_weakAny = _init_l_LLVM_Linkage_weakAny();
l_LLVM_Linkage_weakODR = _init_l_LLVM_Linkage_weakODR();
l_LLVM_Linkage_appending = _init_l_LLVM_Linkage_appending();
l_LLVM_Linkage_internal = _init_l_LLVM_Linkage_internal();
l_LLVM_Linkage_private = _init_l_LLVM_Linkage_private();
l_LLVM_Linkage_dllImport = _init_l_LLVM_Linkage_dllImport();
l_LLVM_Linkage_dllExport = _init_l_LLVM_Linkage_dllExport();
l_LLVM_Linkage_externalWeak = _init_l_LLVM_Linkage_externalWeak();
l_LLVM_Linkage_ghost = _init_l_LLVM_Linkage_ghost();
l_LLVM_Linkage_common = _init_l_LLVM_Linkage_common();
l_LLVM_Linkage_linkerPrivate = _init_l_LLVM_Linkage_linkerPrivate();
l_LLVM_Linkage_linkerPrivateWeak = _init_l_LLVM_Linkage_linkerPrivateWeak();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_LLVMBindings(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_LLVMBindings(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_LLVMBindings(builtin);
}
#ifdef __cplusplus
}
#endif
