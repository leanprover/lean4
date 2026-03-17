// Lean compiler output
// Module: Lean.Compiler.IR.LLVMBindings
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
LEAN_EXPORT lean_object* l_LLVM_constString___boxed(lean_object* v_ctx_291_, lean_object* v_str_292_, lean_object* v_a_00___x40___internal___hyg_293_){
_start:
{
size_t v_ctx_boxed_294_; size_t v_res_295_; lean_object* v_r_296_; 
v_ctx_boxed_294_ = lean_unbox_usize(v_ctx_291_);
lean_dec(v_ctx_291_);
v_res_295_ = lean_llvm_const_string(v_ctx_boxed_294_, v_str_292_);
lean_dec_ref(v_str_292_);
v_r_296_ = lean_box_usize(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constPointerNull___boxed(lean_object* v_ctx_300_, lean_object* v_elemty_301_, lean_object* v_a_00___x40___internal___hyg_302_){
_start:
{
size_t v_ctx_boxed_303_; size_t v_elemty_boxed_304_; size_t v_res_305_; lean_object* v_r_306_; 
v_ctx_boxed_303_ = lean_unbox_usize(v_ctx_300_);
lean_dec(v_ctx_300_);
v_elemty_boxed_304_ = lean_unbox_usize(v_elemty_301_);
lean_dec(v_elemty_301_);
v_res_305_ = lean_llvm_const_pointer_null(v_ctx_boxed_303_, v_elemty_boxed_304_);
v_r_306_ = lean_box_usize(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getUndef___boxed(lean_object* v_ctx_310_, lean_object* v_elemty_311_, lean_object* v_a_00___x40___internal___hyg_312_){
_start:
{
size_t v_ctx_boxed_313_; size_t v_elemty_boxed_314_; size_t v_res_315_; lean_object* v_r_316_; 
v_ctx_boxed_313_ = lean_unbox_usize(v_ctx_310_);
lean_dec(v_ctx_310_);
v_elemty_boxed_314_ = lean_unbox_usize(v_elemty_311_);
lean_dec(v_elemty_311_);
v_res_315_ = lean_llvm_get_undef(v_ctx_boxed_313_, v_elemty_boxed_314_);
v_r_316_ = lean_box_usize(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createBuilderInContext___boxed(lean_object* v_ctx_319_, lean_object* v_a_00___x40___internal___hyg_320_){
_start:
{
size_t v_ctx_boxed_321_; size_t v_res_322_; lean_object* v_r_323_; 
v_ctx_boxed_321_ = lean_unbox_usize(v_ctx_319_);
lean_dec(v_ctx_319_);
v_res_322_ = lean_llvm_create_builder_in_context(v_ctx_boxed_321_);
v_r_323_ = lean_box_usize(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_LLVM_appendBasicBlockInContext___boxed(lean_object* v_ctx_328_, lean_object* v_fn_329_, lean_object* v_name_330_, lean_object* v_a_00___x40___internal___hyg_331_){
_start:
{
size_t v_ctx_boxed_332_; size_t v_fn_boxed_333_; size_t v_res_334_; lean_object* v_r_335_; 
v_ctx_boxed_332_ = lean_unbox_usize(v_ctx_328_);
lean_dec(v_ctx_328_);
v_fn_boxed_333_ = lean_unbox_usize(v_fn_329_);
lean_dec(v_fn_329_);
v_res_334_ = lean_llvm_append_basic_block_in_context(v_ctx_boxed_332_, v_fn_boxed_333_, v_name_330_);
lean_dec_ref(v_name_330_);
v_r_335_ = lean_box_usize(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_LLVM_countBasicBlocks___boxed(lean_object* v_ctx_339_, lean_object* v_fn_340_, lean_object* v_a_00___x40___internal___hyg_341_){
_start:
{
size_t v_ctx_boxed_342_; size_t v_fn_boxed_343_; uint64_t v_res_344_; lean_object* v_r_345_; 
v_ctx_boxed_342_ = lean_unbox_usize(v_ctx_339_);
lean_dec(v_ctx_339_);
v_fn_boxed_343_ = lean_unbox_usize(v_fn_340_);
lean_dec(v_fn_340_);
v_res_344_ = lean_llvm_count_basic_blocks(v_ctx_boxed_342_, v_fn_boxed_343_);
v_r_345_ = lean_box_uint64(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getEntryBasicBlock___boxed(lean_object* v_ctx_349_, lean_object* v_fn_350_, lean_object* v_a_00___x40___internal___hyg_351_){
_start:
{
size_t v_ctx_boxed_352_; size_t v_fn_boxed_353_; size_t v_res_354_; lean_object* v_r_355_; 
v_ctx_boxed_352_ = lean_unbox_usize(v_ctx_349_);
lean_dec(v_ctx_349_);
v_fn_boxed_353_ = lean_unbox_usize(v_fn_350_);
lean_dec(v_fn_350_);
v_res_354_ = lean_llvm_get_entry_basic_block(v_ctx_boxed_352_, v_fn_boxed_353_);
v_r_355_ = lean_box_usize(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getFirstInstruction___boxed(lean_object* v_ctx_359_, lean_object* v_bb_360_, lean_object* v_a_00___x40___internal___hyg_361_){
_start:
{
size_t v_ctx_boxed_362_; size_t v_bb_boxed_363_; lean_object* v_res_364_; 
v_ctx_boxed_362_ = lean_unbox_usize(v_ctx_359_);
lean_dec(v_ctx_359_);
v_bb_boxed_363_ = lean_unbox_usize(v_bb_360_);
lean_dec(v_bb_360_);
v_res_364_ = lean_llvm_get_first_instruction(v_ctx_boxed_362_, v_bb_boxed_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_LLVM_positionBuilderBefore___boxed(lean_object* v_ctx_369_, lean_object* v_builder_370_, lean_object* v_instr_371_, lean_object* v_a_00___x40___internal___hyg_372_){
_start:
{
size_t v_ctx_boxed_373_; size_t v_builder_boxed_374_; size_t v_instr_boxed_375_; lean_object* v_res_376_; 
v_ctx_boxed_373_ = lean_unbox_usize(v_ctx_369_);
lean_dec(v_ctx_369_);
v_builder_boxed_374_ = lean_unbox_usize(v_builder_370_);
lean_dec(v_builder_370_);
v_instr_boxed_375_ = lean_unbox_usize(v_instr_371_);
lean_dec(v_instr_371_);
v_res_376_ = lean_llvm_position_builder_before(v_ctx_boxed_373_, v_builder_boxed_374_, v_instr_boxed_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_LLVM_positionBuilderAtEnd___boxed(lean_object* v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_2945912803____hygCtx___hyg_382_, lean_object* v_ctx_383_, lean_object* v_builder_384_, lean_object* v_bb_385_, lean_object* v_a_00___x40___internal___hyg_386_){
_start:
{
size_t v_builder_boxed_387_; size_t v_bb_boxed_388_; lean_object* v_res_389_; 
v_builder_boxed_387_ = lean_unbox_usize(v_builder_384_);
lean_dec(v_builder_384_);
v_bb_boxed_388_ = lean_unbox_usize(v_bb_385_);
lean_dec(v_bb_385_);
v_res_389_ = lean_llvm_position_builder_at_end(v_ctx_383_, v_builder_boxed_387_, v_bb_boxed_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCall2___boxed(lean_object* v_ctx_397_, lean_object* v_builder_398_, lean_object* v_ty_399_, lean_object* v_fn_400_, lean_object* v_args_401_, lean_object* v_name_402_, lean_object* v_a_00___x40___internal___hyg_403_){
_start:
{
size_t v_ctx_boxed_404_; size_t v_builder_boxed_405_; size_t v_ty_boxed_406_; size_t v_fn_boxed_407_; size_t v_res_408_; lean_object* v_r_409_; 
v_ctx_boxed_404_ = lean_unbox_usize(v_ctx_397_);
lean_dec(v_ctx_397_);
v_builder_boxed_405_ = lean_unbox_usize(v_builder_398_);
lean_dec(v_builder_398_);
v_ty_boxed_406_ = lean_unbox_usize(v_ty_399_);
lean_dec(v_ty_399_);
v_fn_boxed_407_ = lean_unbox_usize(v_fn_400_);
lean_dec(v_fn_400_);
v_res_408_ = lean_llvm_build_call2(v_ctx_boxed_404_, v_builder_boxed_405_, v_ty_boxed_406_, v_fn_boxed_407_, v_args_401_, v_name_402_);
lean_dec_ref(v_args_401_);
v_r_409_ = lean_box_usize(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setTailCall___boxed(lean_object* v_ctx_414_, lean_object* v_fn_415_, lean_object* v_istail_416_, lean_object* v_a_00___x40___internal___hyg_417_){
_start:
{
size_t v_ctx_boxed_418_; size_t v_fn_boxed_419_; uint8_t v_istail_boxed_420_; lean_object* v_res_421_; 
v_ctx_boxed_418_ = lean_unbox_usize(v_ctx_414_);
lean_dec(v_ctx_414_);
v_fn_boxed_419_ = lean_unbox_usize(v_fn_415_);
lean_dec(v_fn_415_);
v_istail_boxed_420_ = lean_unbox(v_istail_416_);
v_res_421_ = lean_llvm_set_tail_call(v_ctx_boxed_418_, v_fn_boxed_419_, v_istail_boxed_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCondBr___boxed(lean_object* v_ctx_428_, lean_object* v_builder_429_, lean_object* v_if___430_, lean_object* v_thenbb_431_, lean_object* v_elsebb_432_, lean_object* v_a_00___x40___internal___hyg_433_){
_start:
{
size_t v_ctx_boxed_434_; size_t v_builder_boxed_435_; size_t v_if___00boxed_436_; size_t v_thenbb_boxed_437_; size_t v_elsebb_boxed_438_; size_t v_res_439_; lean_object* v_r_440_; 
v_ctx_boxed_434_ = lean_unbox_usize(v_ctx_428_);
lean_dec(v_ctx_428_);
v_builder_boxed_435_ = lean_unbox_usize(v_builder_429_);
lean_dec(v_builder_429_);
v_if___00boxed_436_ = lean_unbox_usize(v_if___430_);
lean_dec(v_if___430_);
v_thenbb_boxed_437_ = lean_unbox_usize(v_thenbb_431_);
lean_dec(v_thenbb_431_);
v_elsebb_boxed_438_ = lean_unbox_usize(v_elsebb_432_);
lean_dec(v_elsebb_432_);
v_res_439_ = lean_llvm_build_cond_br(v_ctx_boxed_434_, v_builder_boxed_435_, v_if___00boxed_436_, v_thenbb_boxed_437_, v_elsebb_boxed_438_);
v_r_440_ = lean_box_usize(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildBr___boxed(lean_object* v_ctx_445_, lean_object* v_builder_446_, lean_object* v_bb_447_, lean_object* v_a_00___x40___internal___hyg_448_){
_start:
{
size_t v_ctx_boxed_449_; size_t v_builder_boxed_450_; size_t v_bb_boxed_451_; size_t v_res_452_; lean_object* v_r_453_; 
v_ctx_boxed_449_ = lean_unbox_usize(v_ctx_445_);
lean_dec(v_ctx_445_);
v_builder_boxed_450_ = lean_unbox_usize(v_builder_446_);
lean_dec(v_builder_446_);
v_bb_boxed_451_ = lean_unbox_usize(v_bb_447_);
lean_dec(v_bb_447_);
v_res_452_ = lean_llvm_build_br(v_ctx_boxed_449_, v_builder_boxed_450_, v_bb_boxed_451_);
v_r_453_ = lean_box_usize(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAlloca___boxed(lean_object* v_ctx_459_, lean_object* v_builder_460_, lean_object* v_ty_461_, lean_object* v_name_462_, lean_object* v_a_00___x40___internal___hyg_463_){
_start:
{
size_t v_ctx_boxed_464_; size_t v_builder_boxed_465_; size_t v_ty_boxed_466_; size_t v_res_467_; lean_object* v_r_468_; 
v_ctx_boxed_464_ = lean_unbox_usize(v_ctx_459_);
lean_dec(v_ctx_459_);
v_builder_boxed_465_ = lean_unbox_usize(v_builder_460_);
lean_dec(v_builder_460_);
v_ty_boxed_466_ = lean_unbox_usize(v_ty_461_);
lean_dec(v_ty_461_);
v_res_467_ = lean_llvm_build_alloca(v_ctx_boxed_464_, v_builder_boxed_465_, v_ty_boxed_466_, v_name_462_);
v_r_468_ = lean_box_usize(v_res_467_);
return v_r_468_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildLoad2___boxed(lean_object* v_ctx_475_, lean_object* v_builder_476_, lean_object* v_ty_477_, lean_object* v_val_478_, lean_object* v_name_479_, lean_object* v_a_00___x40___internal___hyg_480_){
_start:
{
size_t v_ctx_boxed_481_; size_t v_builder_boxed_482_; size_t v_ty_boxed_483_; size_t v_val_boxed_484_; size_t v_res_485_; lean_object* v_r_486_; 
v_ctx_boxed_481_ = lean_unbox_usize(v_ctx_475_);
lean_dec(v_ctx_475_);
v_builder_boxed_482_ = lean_unbox_usize(v_builder_476_);
lean_dec(v_builder_476_);
v_ty_boxed_483_ = lean_unbox_usize(v_ty_477_);
lean_dec(v_ty_477_);
v_val_boxed_484_ = lean_unbox_usize(v_val_478_);
lean_dec(v_val_478_);
v_res_485_ = lean_llvm_build_load2(v_ctx_boxed_481_, v_builder_boxed_482_, v_ty_boxed_483_, v_val_boxed_484_, v_name_479_);
v_r_486_ = lean_box_usize(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildStore___boxed(lean_object* v_ctx_492_, lean_object* v_builder_493_, lean_object* v_val_494_, lean_object* v_store__loc__ptr_495_, lean_object* v_a_00___x40___internal___hyg_496_){
_start:
{
size_t v_ctx_boxed_497_; size_t v_builder_boxed_498_; size_t v_val_boxed_499_; size_t v_store__loc__ptr_boxed_500_; lean_object* v_res_501_; 
v_ctx_boxed_497_ = lean_unbox_usize(v_ctx_492_);
lean_dec(v_ctx_492_);
v_builder_boxed_498_ = lean_unbox_usize(v_builder_493_);
lean_dec(v_builder_493_);
v_val_boxed_499_ = lean_unbox_usize(v_val_494_);
lean_dec(v_val_494_);
v_store__loc__ptr_boxed_500_ = lean_unbox_usize(v_store__loc__ptr_495_);
lean_dec(v_store__loc__ptr_495_);
v_res_501_ = lean_llvm_build_store(v_ctx_boxed_497_, v_builder_boxed_498_, v_val_boxed_499_, v_store__loc__ptr_boxed_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildRet___boxed(lean_object* v_ctx_506_, lean_object* v_builder_507_, lean_object* v_val_508_, lean_object* v_a_00___x40___internal___hyg_509_){
_start:
{
size_t v_ctx_boxed_510_; size_t v_builder_boxed_511_; size_t v_val_boxed_512_; size_t v_res_513_; lean_object* v_r_514_; 
v_ctx_boxed_510_ = lean_unbox_usize(v_ctx_506_);
lean_dec(v_ctx_506_);
v_builder_boxed_511_ = lean_unbox_usize(v_builder_507_);
lean_dec(v_builder_507_);
v_val_boxed_512_ = lean_unbox_usize(v_val_508_);
lean_dec(v_val_508_);
v_res_513_ = lean_llvm_build_ret(v_ctx_boxed_510_, v_builder_boxed_511_, v_val_boxed_512_);
v_r_514_ = lean_box_usize(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildUnreachable___boxed(lean_object* v_ctx_518_, lean_object* v_builder_519_, lean_object* v_a_00___x40___internal___hyg_520_){
_start:
{
size_t v_ctx_boxed_521_; size_t v_builder_boxed_522_; size_t v_res_523_; lean_object* v_r_524_; 
v_ctx_boxed_521_ = lean_unbox_usize(v_ctx_518_);
lean_dec(v_ctx_518_);
v_builder_boxed_522_ = lean_unbox_usize(v_builder_519_);
lean_dec(v_builder_519_);
v_res_523_ = lean_llvm_build_unreachable(v_ctx_boxed_521_, v_builder_boxed_522_);
v_r_524_ = lean_box_usize(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildGEP2___boxed(lean_object* v_ctx_532_, lean_object* v_builder_533_, lean_object* v_ty_534_, lean_object* v_base_535_, lean_object* v_ixs_536_, lean_object* v_name_537_, lean_object* v_a_00___x40___internal___hyg_538_){
_start:
{
size_t v_ctx_boxed_539_; size_t v_builder_boxed_540_; size_t v_ty_boxed_541_; size_t v_base_boxed_542_; size_t v_res_543_; lean_object* v_r_544_; 
v_ctx_boxed_539_ = lean_unbox_usize(v_ctx_532_);
lean_dec(v_ctx_532_);
v_builder_boxed_540_ = lean_unbox_usize(v_builder_533_);
lean_dec(v_builder_533_);
v_ty_boxed_541_ = lean_unbox_usize(v_ty_534_);
lean_dec(v_ty_534_);
v_base_boxed_542_ = lean_unbox_usize(v_base_535_);
lean_dec(v_base_535_);
v_res_543_ = lean_llvm_build_gep2(v_ctx_boxed_539_, v_builder_boxed_540_, v_ty_boxed_541_, v_base_boxed_542_, v_ixs_536_, v_name_537_);
lean_dec_ref(v_ixs_536_);
v_r_544_ = lean_box_usize(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildInBoundsGEP2___boxed(lean_object* v_ctx_552_, lean_object* v_builder_553_, lean_object* v_ty_554_, lean_object* v_base_555_, lean_object* v_ixs_556_, lean_object* v_name_557_, lean_object* v_a_00___x40___internal___hyg_558_){
_start:
{
size_t v_ctx_boxed_559_; size_t v_builder_boxed_560_; size_t v_ty_boxed_561_; size_t v_base_boxed_562_; size_t v_res_563_; lean_object* v_r_564_; 
v_ctx_boxed_559_ = lean_unbox_usize(v_ctx_552_);
lean_dec(v_ctx_552_);
v_builder_boxed_560_ = lean_unbox_usize(v_builder_553_);
lean_dec(v_builder_553_);
v_ty_boxed_561_ = lean_unbox_usize(v_ty_554_);
lean_dec(v_ty_554_);
v_base_boxed_562_ = lean_unbox_usize(v_base_555_);
lean_dec(v_base_555_);
v_res_563_ = lean_llvm_build_inbounds_gep2(v_ctx_boxed_559_, v_builder_boxed_560_, v_ty_boxed_561_, v_base_boxed_562_, v_ixs_556_, v_name_557_);
lean_dec_ref(v_ixs_556_);
v_r_564_ = lean_box_usize(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSext___boxed(lean_object* v_ctx_571_, lean_object* v_builder_572_, lean_object* v_val_573_, lean_object* v_destTy_574_, lean_object* v_name_575_, lean_object* v_a_00___x40___internal___hyg_576_){
_start:
{
size_t v_ctx_boxed_577_; size_t v_builder_boxed_578_; size_t v_val_boxed_579_; size_t v_destTy_boxed_580_; size_t v_res_581_; lean_object* v_r_582_; 
v_ctx_boxed_577_ = lean_unbox_usize(v_ctx_571_);
lean_dec(v_ctx_571_);
v_builder_boxed_578_ = lean_unbox_usize(v_builder_572_);
lean_dec(v_builder_572_);
v_val_boxed_579_ = lean_unbox_usize(v_val_573_);
lean_dec(v_val_573_);
v_destTy_boxed_580_ = lean_unbox_usize(v_destTy_574_);
lean_dec(v_destTy_574_);
v_res_581_ = lean_llvm_build_sext(v_ctx_boxed_577_, v_builder_boxed_578_, v_val_boxed_579_, v_destTy_boxed_580_, v_name_575_);
v_r_582_ = lean_box_usize(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildZext___boxed(lean_object* v_ctx_589_, lean_object* v_builder_590_, lean_object* v_val_591_, lean_object* v_destTy_592_, lean_object* v_name_593_, lean_object* v_a_00___x40___internal___hyg_594_){
_start:
{
size_t v_ctx_boxed_595_; size_t v_builder_boxed_596_; size_t v_val_boxed_597_; size_t v_destTy_boxed_598_; size_t v_res_599_; lean_object* v_r_600_; 
v_ctx_boxed_595_ = lean_unbox_usize(v_ctx_589_);
lean_dec(v_ctx_589_);
v_builder_boxed_596_ = lean_unbox_usize(v_builder_590_);
lean_dec(v_builder_590_);
v_val_boxed_597_ = lean_unbox_usize(v_val_591_);
lean_dec(v_val_591_);
v_destTy_boxed_598_ = lean_unbox_usize(v_destTy_592_);
lean_dec(v_destTy_592_);
v_res_599_ = lean_llvm_build_zext(v_ctx_boxed_595_, v_builder_boxed_596_, v_val_boxed_597_, v_destTy_boxed_598_, v_name_593_);
v_r_600_ = lean_box_usize(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSextOrTrunc___boxed(lean_object* v_ctx_607_, lean_object* v_builder_608_, lean_object* v_val_609_, lean_object* v_destTy_610_, lean_object* v_name_611_, lean_object* v_a_00___x40___internal___hyg_612_){
_start:
{
size_t v_ctx_boxed_613_; size_t v_builder_boxed_614_; size_t v_val_boxed_615_; size_t v_destTy_boxed_616_; size_t v_res_617_; lean_object* v_r_618_; 
v_ctx_boxed_613_ = lean_unbox_usize(v_ctx_607_);
lean_dec(v_ctx_607_);
v_builder_boxed_614_ = lean_unbox_usize(v_builder_608_);
lean_dec(v_builder_608_);
v_val_boxed_615_ = lean_unbox_usize(v_val_609_);
lean_dec(v_val_609_);
v_destTy_boxed_616_ = lean_unbox_usize(v_destTy_610_);
lean_dec(v_destTy_610_);
v_res_617_ = lean_llvm_build_sext_or_trunc(v_ctx_boxed_613_, v_builder_boxed_614_, v_val_boxed_615_, v_destTy_boxed_616_, v_name_611_);
v_r_618_ = lean_box_usize(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSwitch___boxed(lean_object* v_ctx_625_, lean_object* v_builder_626_, lean_object* v_val_627_, lean_object* v_elseBB_628_, lean_object* v_numCasesHint_629_, lean_object* v_a_00___x40___internal___hyg_630_){
_start:
{
size_t v_ctx_boxed_631_; size_t v_builder_boxed_632_; size_t v_val_boxed_633_; size_t v_elseBB_boxed_634_; uint64_t v_numCasesHint_boxed_635_; size_t v_res_636_; lean_object* v_r_637_; 
v_ctx_boxed_631_ = lean_unbox_usize(v_ctx_625_);
lean_dec(v_ctx_625_);
v_builder_boxed_632_ = lean_unbox_usize(v_builder_626_);
lean_dec(v_builder_626_);
v_val_boxed_633_ = lean_unbox_usize(v_val_627_);
lean_dec(v_val_627_);
v_elseBB_boxed_634_ = lean_unbox_usize(v_elseBB_628_);
lean_dec(v_elseBB_628_);
v_numCasesHint_boxed_635_ = lean_unbox_uint64(v_numCasesHint_629_);
lean_dec_ref(v_numCasesHint_629_);
v_res_636_ = lean_llvm_build_switch(v_ctx_boxed_631_, v_builder_boxed_632_, v_val_boxed_633_, v_elseBB_boxed_634_, v_numCasesHint_boxed_635_);
v_r_637_ = lean_box_usize(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildPtrToInt___boxed(lean_object* v_ctx_644_, lean_object* v_builder_645_, lean_object* v_ptr_646_, lean_object* v_destTy_647_, lean_object* v_name_648_, lean_object* v_a_00___x40___internal___hyg_649_){
_start:
{
size_t v_ctx_boxed_650_; size_t v_builder_boxed_651_; size_t v_ptr_boxed_652_; size_t v_destTy_boxed_653_; size_t v_res_654_; lean_object* v_r_655_; 
v_ctx_boxed_650_ = lean_unbox_usize(v_ctx_644_);
lean_dec(v_ctx_644_);
v_builder_boxed_651_ = lean_unbox_usize(v_builder_645_);
lean_dec(v_builder_645_);
v_ptr_boxed_652_ = lean_unbox_usize(v_ptr_646_);
lean_dec(v_ptr_646_);
v_destTy_boxed_653_ = lean_unbox_usize(v_destTy_647_);
lean_dec(v_destTy_647_);
v_res_654_ = lean_llvm_build_ptr_to_int(v_ctx_boxed_650_, v_builder_boxed_651_, v_ptr_boxed_652_, v_destTy_boxed_653_, v_name_648_);
v_r_655_ = lean_box_usize(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildMul___boxed(lean_object* v_ctx_662_, lean_object* v_builder_663_, lean_object* v_x_664_, lean_object* v_y_665_, lean_object* v_name_666_, lean_object* v_a_00___x40___internal___hyg_667_){
_start:
{
size_t v_ctx_boxed_668_; size_t v_builder_boxed_669_; size_t v_x_boxed_670_; size_t v_y_boxed_671_; size_t v_res_672_; lean_object* v_r_673_; 
v_ctx_boxed_668_ = lean_unbox_usize(v_ctx_662_);
lean_dec(v_ctx_662_);
v_builder_boxed_669_ = lean_unbox_usize(v_builder_663_);
lean_dec(v_builder_663_);
v_x_boxed_670_ = lean_unbox_usize(v_x_664_);
lean_dec(v_x_664_);
v_y_boxed_671_ = lean_unbox_usize(v_y_665_);
lean_dec(v_y_665_);
v_res_672_ = lean_llvm_build_mul(v_ctx_boxed_668_, v_builder_boxed_669_, v_x_boxed_670_, v_y_boxed_671_, v_name_666_);
v_r_673_ = lean_box_usize(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAdd___boxed(lean_object* v_ctx_680_, lean_object* v_builder_681_, lean_object* v_x_682_, lean_object* v_y_683_, lean_object* v_name_684_, lean_object* v_a_00___x40___internal___hyg_685_){
_start:
{
size_t v_ctx_boxed_686_; size_t v_builder_boxed_687_; size_t v_x_boxed_688_; size_t v_y_boxed_689_; size_t v_res_690_; lean_object* v_r_691_; 
v_ctx_boxed_686_ = lean_unbox_usize(v_ctx_680_);
lean_dec(v_ctx_680_);
v_builder_boxed_687_ = lean_unbox_usize(v_builder_681_);
lean_dec(v_builder_681_);
v_x_boxed_688_ = lean_unbox_usize(v_x_682_);
lean_dec(v_x_682_);
v_y_boxed_689_ = lean_unbox_usize(v_y_683_);
lean_dec(v_y_683_);
v_res_690_ = lean_llvm_build_add(v_ctx_boxed_686_, v_builder_boxed_687_, v_x_boxed_688_, v_y_boxed_689_, v_name_684_);
v_r_691_ = lean_box_usize(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSub___boxed(lean_object* v_ctx_698_, lean_object* v_builder_699_, lean_object* v_x_700_, lean_object* v_y_701_, lean_object* v_name_702_, lean_object* v_a_00___x40___internal___hyg_703_){
_start:
{
size_t v_ctx_boxed_704_; size_t v_builder_boxed_705_; size_t v_x_boxed_706_; size_t v_y_boxed_707_; size_t v_res_708_; lean_object* v_r_709_; 
v_ctx_boxed_704_ = lean_unbox_usize(v_ctx_698_);
lean_dec(v_ctx_698_);
v_builder_boxed_705_ = lean_unbox_usize(v_builder_699_);
lean_dec(v_builder_699_);
v_x_boxed_706_ = lean_unbox_usize(v_x_700_);
lean_dec(v_x_700_);
v_y_boxed_707_ = lean_unbox_usize(v_y_701_);
lean_dec(v_y_701_);
v_res_708_ = lean_llvm_build_sub(v_ctx_boxed_704_, v_builder_boxed_705_, v_x_boxed_706_, v_y_boxed_707_, v_name_702_);
v_r_709_ = lean_box_usize(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildNot___boxed(lean_object* v_ctx_715_, lean_object* v_builder_716_, lean_object* v_x_717_, lean_object* v_name_718_, lean_object* v_a_00___x40___internal___hyg_719_){
_start:
{
size_t v_ctx_boxed_720_; size_t v_builder_boxed_721_; size_t v_x_boxed_722_; size_t v_res_723_; lean_object* v_r_724_; 
v_ctx_boxed_720_ = lean_unbox_usize(v_ctx_715_);
lean_dec(v_ctx_715_);
v_builder_boxed_721_ = lean_unbox_usize(v_builder_716_);
lean_dec(v_builder_716_);
v_x_boxed_722_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_723_ = lean_llvm_build_not(v_ctx_boxed_720_, v_builder_boxed_721_, v_x_boxed_722_, v_name_718_);
v_r_724_ = lean_box_usize(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildICmp___boxed(lean_object* v_ctx_732_, lean_object* v_builder_733_, lean_object* v_predicate_734_, lean_object* v_x_735_, lean_object* v_y_736_, lean_object* v_name_737_, lean_object* v_a_00___x40___internal___hyg_738_){
_start:
{
size_t v_ctx_boxed_739_; size_t v_builder_boxed_740_; uint64_t v_predicate_boxed_741_; size_t v_x_boxed_742_; size_t v_y_boxed_743_; size_t v_res_744_; lean_object* v_r_745_; 
v_ctx_boxed_739_ = lean_unbox_usize(v_ctx_732_);
lean_dec(v_ctx_732_);
v_builder_boxed_740_ = lean_unbox_usize(v_builder_733_);
lean_dec(v_builder_733_);
v_predicate_boxed_741_ = lean_unbox_uint64(v_predicate_734_);
lean_dec_ref(v_predicate_734_);
v_x_boxed_742_ = lean_unbox_usize(v_x_735_);
lean_dec(v_x_735_);
v_y_boxed_743_ = lean_unbox_usize(v_y_736_);
lean_dec(v_y_736_);
v_res_744_ = lean_llvm_build_icmp(v_ctx_boxed_739_, v_builder_boxed_740_, v_predicate_boxed_741_, v_x_boxed_742_, v_y_boxed_743_, v_name_737_);
v_r_745_ = lean_box_usize(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addCase___boxed(lean_object* v_ctx_751_, lean_object* v_switch_752_, lean_object* v_onVal_753_, lean_object* v_destBB_754_, lean_object* v_a_00___x40___internal___hyg_755_){
_start:
{
size_t v_ctx_boxed_756_; size_t v_switch_boxed_757_; size_t v_onVal_boxed_758_; size_t v_destBB_boxed_759_; lean_object* v_res_760_; 
v_ctx_boxed_756_ = lean_unbox_usize(v_ctx_751_);
lean_dec(v_ctx_751_);
v_switch_boxed_757_ = lean_unbox_usize(v_switch_752_);
lean_dec(v_switch_752_);
v_onVal_boxed_758_ = lean_unbox_usize(v_onVal_753_);
lean_dec(v_onVal_753_);
v_destBB_boxed_759_ = lean_unbox_usize(v_destBB_754_);
lean_dec(v_destBB_754_);
v_res_760_ = lean_llvm_add_case(v_ctx_boxed_756_, v_switch_boxed_757_, v_onVal_boxed_758_, v_destBB_boxed_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getInsertBlock___boxed(lean_object* v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_924321998____hygCtx___hyg_765_, lean_object* v_ctx_766_, lean_object* v_builder_767_, lean_object* v_a_00___x40___internal___hyg_768_){
_start:
{
size_t v_builder_boxed_769_; size_t v_res_770_; lean_object* v_r_771_; 
v_builder_boxed_769_ = lean_unbox_usize(v_builder_767_);
lean_dec(v_builder_767_);
v_res_770_ = lean_llvm_get_insert_block(v_ctx_766_, v_builder_boxed_769_);
v_r_771_ = lean_box_usize(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT lean_object* l_LLVM_clearInsertionPosition___boxed(lean_object* v_Context_00___x40_Lean_Compiler_IR_LLVMBindings_1700267677____hygCtx___hyg_776_, lean_object* v_ctx_777_, lean_object* v_builder_778_, lean_object* v_a_00___x40___internal___hyg_779_){
_start:
{
size_t v_builder_boxed_780_; lean_object* v_res_781_; 
v_builder_boxed_780_ = lean_unbox_usize(v_builder_778_);
lean_dec(v_builder_778_);
v_res_781_ = lean_llvm_clear_insertion_position(v_ctx_777_, v_builder_boxed_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getBasicBlockParent___boxed(lean_object* v_ctx_785_, lean_object* v_bb_786_, lean_object* v_a_00___x40___internal___hyg_787_){
_start:
{
size_t v_ctx_boxed_788_; size_t v_bb_boxed_789_; size_t v_res_790_; lean_object* v_r_791_; 
v_ctx_boxed_788_ = lean_unbox_usize(v_ctx_785_);
lean_dec(v_ctx_785_);
v_bb_boxed_789_ = lean_unbox_usize(v_bb_786_);
lean_dec(v_bb_786_);
v_res_790_ = lean_llvm_get_basic_block_parent(v_ctx_boxed_788_, v_bb_boxed_789_);
v_r_791_ = lean_box_usize(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_LLVM_typeOf___boxed(lean_object* v_ctx_795_, lean_object* v_val_796_, lean_object* v_a_00___x40___internal___hyg_797_){
_start:
{
size_t v_ctx_boxed_798_; size_t v_val_boxed_799_; size_t v_res_800_; lean_object* v_r_801_; 
v_ctx_boxed_798_ = lean_unbox_usize(v_ctx_795_);
lean_dec(v_ctx_795_);
v_val_boxed_799_ = lean_unbox_usize(v_val_796_);
lean_dec(v_val_796_);
v_res_800_ = lean_llvm_type_of(v_ctx_boxed_798_, v_val_boxed_799_);
v_r_801_ = lean_box_usize(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt___boxed(lean_object* v_ctx_807_, lean_object* v_intty_808_, lean_object* v_value_809_, lean_object* v_signExtend_810_, lean_object* v_a_00___x40___internal___hyg_811_){
_start:
{
size_t v_ctx_boxed_812_; size_t v_intty_boxed_813_; uint64_t v_value_boxed_814_; uint8_t v_signExtend_boxed_815_; size_t v_res_816_; lean_object* v_r_817_; 
v_ctx_boxed_812_ = lean_unbox_usize(v_ctx_807_);
lean_dec(v_ctx_807_);
v_intty_boxed_813_ = lean_unbox_usize(v_intty_808_);
lean_dec(v_intty_808_);
v_value_boxed_814_ = lean_unbox_uint64(v_value_809_);
lean_dec_ref(v_value_809_);
v_signExtend_boxed_815_ = lean_unbox(v_signExtend_810_);
v_res_816_ = lean_llvm_const_int(v_ctx_boxed_812_, v_intty_boxed_813_, v_value_boxed_814_, v_signExtend_boxed_815_);
v_r_817_ = lean_box_usize(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoString___boxed(lean_object* v_ctx_821_, lean_object* v_mod_822_, lean_object* v_a_00___x40___internal___hyg_823_){
_start:
{
size_t v_ctx_boxed_824_; size_t v_mod_boxed_825_; lean_object* v_res_826_; 
v_ctx_boxed_824_ = lean_unbox_usize(v_ctx_821_);
lean_dec(v_ctx_821_);
v_mod_boxed_825_ = lean_unbox_usize(v_mod_822_);
lean_dec(v_mod_822_);
v_res_826_ = lean_llvm_print_module_to_string(v_ctx_boxed_824_, v_mod_boxed_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoFile___boxed(lean_object* v_ctx_831_, lean_object* v_mod_832_, lean_object* v_file_833_, lean_object* v_a_00___x40___internal___hyg_834_){
_start:
{
size_t v_ctx_boxed_835_; size_t v_mod_boxed_836_; lean_object* v_res_837_; 
v_ctx_boxed_835_ = lean_unbox_usize(v_ctx_831_);
lean_dec(v_ctx_831_);
v_mod_boxed_836_ = lean_unbox_usize(v_mod_832_);
lean_dec(v_mod_832_);
v_res_837_ = lean_llvm_print_module_to_file(v_ctx_boxed_835_, v_mod_boxed_836_, v_file_833_);
lean_dec_ref(v_file_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_LLVM_countParams___boxed(lean_object* v_ctx_841_, lean_object* v_fn_842_, lean_object* v_a_00___x40___internal___hyg_843_){
_start:
{
size_t v_ctx_boxed_844_; size_t v_fn_boxed_845_; uint64_t v_res_846_; lean_object* v_r_847_; 
v_ctx_boxed_844_ = lean_unbox_usize(v_ctx_841_);
lean_dec(v_ctx_841_);
v_fn_boxed_845_ = lean_unbox_usize(v_fn_842_);
lean_dec(v_fn_842_);
v_res_846_ = llvm_count_params(v_ctx_boxed_844_, v_fn_boxed_845_);
v_r_847_ = lean_box_uint64(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getParam___boxed(lean_object* v_ctx_852_, lean_object* v_fn_853_, lean_object* v_ix_854_, lean_object* v_a_00___x40___internal___hyg_855_){
_start:
{
size_t v_ctx_boxed_856_; size_t v_fn_boxed_857_; uint64_t v_ix_boxed_858_; size_t v_res_859_; lean_object* v_r_860_; 
v_ctx_boxed_856_ = lean_unbox_usize(v_ctx_852_);
lean_dec(v_ctx_852_);
v_fn_boxed_857_ = lean_unbox_usize(v_fn_853_);
lean_dec(v_fn_853_);
v_ix_boxed_858_ = lean_unbox_uint64(v_ix_854_);
lean_dec_ref(v_ix_854_);
v_res_859_ = llvm_get_param(v_ctx_boxed_856_, v_fn_boxed_857_, v_ix_boxed_858_);
v_r_860_ = lean_box_usize(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createMemoryBufferWithContentsOfFile___boxed(lean_object* v_ctx_864_, lean_object* v_path_865_, lean_object* v_a_00___x40___internal___hyg_866_){
_start:
{
size_t v_ctx_boxed_867_; size_t v_res_868_; lean_object* v_r_869_; 
v_ctx_boxed_867_ = lean_unbox_usize(v_ctx_864_);
lean_dec(v_ctx_864_);
v_res_868_ = lean_llvm_create_memory_buffer_with_contents_of_file(v_ctx_boxed_867_, v_path_865_);
lean_dec_ref(v_path_865_);
v_r_869_ = lean_box_usize(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l_LLVM_parseBitcode___boxed(lean_object* v_ctx_873_, lean_object* v_membuf_874_, lean_object* v_a_00___x40___internal___hyg_875_){
_start:
{
size_t v_ctx_boxed_876_; size_t v_membuf_boxed_877_; size_t v_res_878_; lean_object* v_r_879_; 
v_ctx_boxed_876_ = lean_unbox_usize(v_ctx_873_);
lean_dec(v_ctx_873_);
v_membuf_boxed_877_ = lean_unbox_usize(v_membuf_874_);
lean_dec(v_membuf_874_);
v_res_878_ = lean_llvm_parse_bitcode(v_ctx_boxed_876_, v_membuf_boxed_877_);
v_r_879_ = lean_box_usize(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_LLVM_linkModules___boxed(lean_object* v_ctx_884_, lean_object* v_dest_885_, lean_object* v_src_886_, lean_object* v_a_00___x40___internal___hyg_887_){
_start:
{
size_t v_ctx_boxed_888_; size_t v_dest_boxed_889_; size_t v_src_boxed_890_; lean_object* v_res_891_; 
v_ctx_boxed_888_ = lean_unbox_usize(v_ctx_884_);
lean_dec(v_ctx_884_);
v_dest_boxed_889_ = lean_unbox_usize(v_dest_885_);
lean_dec(v_dest_885_);
v_src_boxed_890_ = lean_unbox_usize(v_src_886_);
lean_dec(v_src_886_);
v_res_891_ = lean_llvm_link_modules(v_ctx_boxed_888_, v_dest_boxed_889_, v_src_boxed_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getDefaultTargetTriple___boxed(lean_object* v_a_00___x40___internal___hyg_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = lean_llvm_get_default_target_triple();
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_LLVM_getTargetFromTriple___boxed(lean_object* v_ctx_898_, lean_object* v_triple_899_, lean_object* v_a_00___x40___internal___hyg_900_){
_start:
{
size_t v_ctx_boxed_901_; size_t v_res_902_; lean_object* v_r_903_; 
v_ctx_boxed_901_ = lean_unbox_usize(v_ctx_898_);
lean_dec(v_ctx_898_);
v_res_902_ = lean_llvm_get_target_from_triple(v_ctx_boxed_901_, v_triple_899_);
lean_dec_ref(v_triple_899_);
v_r_903_ = lean_box_usize(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createTargetMachine___boxed(lean_object* v_ctx_910_, lean_object* v_target_911_, lean_object* v_tripleStr_912_, lean_object* v_cpu_913_, lean_object* v_features_914_, lean_object* v_a_00___x40___internal___hyg_915_){
_start:
{
size_t v_ctx_boxed_916_; size_t v_target_boxed_917_; size_t v_res_918_; lean_object* v_r_919_; 
v_ctx_boxed_916_ = lean_unbox_usize(v_ctx_910_);
lean_dec(v_ctx_910_);
v_target_boxed_917_ = lean_unbox_usize(v_target_911_);
lean_dec(v_target_911_);
v_res_918_ = lean_llvm_create_target_machine(v_ctx_boxed_916_, v_target_boxed_917_, v_tripleStr_912_, v_cpu_913_, v_features_914_);
lean_dec_ref(v_features_914_);
lean_dec_ref(v_cpu_913_);
lean_dec_ref(v_tripleStr_912_);
v_r_919_ = lean_box_usize(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_LLVM_targetMachineEmitToFile___boxed(lean_object* v_ctx_926_, lean_object* v_targetMachine_927_, lean_object* v_module_928_, lean_object* v_filepath_929_, lean_object* v_codegenType_930_, lean_object* v_a_00___x40___internal___hyg_931_){
_start:
{
size_t v_ctx_boxed_932_; size_t v_targetMachine_boxed_933_; size_t v_module_boxed_934_; uint64_t v_codegenType_boxed_935_; lean_object* v_res_936_; 
v_ctx_boxed_932_ = lean_unbox_usize(v_ctx_926_);
lean_dec(v_ctx_926_);
v_targetMachine_boxed_933_ = lean_unbox_usize(v_targetMachine_927_);
lean_dec(v_targetMachine_927_);
v_module_boxed_934_ = lean_unbox_usize(v_module_928_);
lean_dec(v_module_928_);
v_codegenType_boxed_935_ = lean_unbox_uint64(v_codegenType_930_);
lean_dec_ref(v_codegenType_930_);
v_res_936_ = lean_llvm_target_machine_emit_to_file(v_ctx_boxed_932_, v_targetMachine_boxed_933_, v_module_boxed_934_, v_filepath_929_, v_codegenType_boxed_935_);
lean_dec_ref(v_filepath_929_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeTargetMachine___boxed(lean_object* v_ctx_940_, lean_object* v_tm_941_, lean_object* v_a_00___x40___internal___hyg_942_){
_start:
{
size_t v_ctx_boxed_943_; size_t v_tm_boxed_944_; lean_object* v_res_945_; 
v_ctx_boxed_943_ = lean_unbox_usize(v_ctx_940_);
lean_dec(v_ctx_940_);
v_tm_boxed_944_ = lean_unbox_usize(v_tm_941_);
lean_dec(v_tm_941_);
v_res_945_ = lean_llvm_dispose_target_machine(v_ctx_boxed_943_, v_tm_boxed_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeModule___boxed(lean_object* v_ctx_949_, lean_object* v_m_950_, lean_object* v_a_00___x40___internal___hyg_951_){
_start:
{
size_t v_ctx_boxed_952_; size_t v_m_boxed_953_; lean_object* v_res_954_; 
v_ctx_boxed_952_ = lean_unbox_usize(v_ctx_949_);
lean_dec(v_ctx_949_);
v_m_boxed_953_ = lean_unbox_usize(v_m_950_);
lean_dec(v_m_950_);
v_res_954_ = lean_llvm_dispose_module(v_ctx_boxed_952_, v_m_boxed_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_LLVM_verifyModule___boxed(lean_object* v_ctx_958_, lean_object* v_m_959_, lean_object* v_a_00___x40___internal___hyg_960_){
_start:
{
size_t v_ctx_boxed_961_; size_t v_m_boxed_962_; lean_object* v_res_963_; 
v_ctx_boxed_961_ = lean_unbox_usize(v_ctx_958_);
lean_dec(v_ctx_958_);
v_m_boxed_962_ = lean_unbox_usize(v_m_959_);
lean_dec(v_m_959_);
v_res_963_ = lean_llvm_verify_module(v_ctx_boxed_961_, v_m_boxed_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_LLVM_createStringAttribute___boxed(lean_object* v_ctx_968_, lean_object* v_key_969_, lean_object* v_value_970_, lean_object* v_a_00___x40___internal___hyg_971_){
_start:
{
size_t v_ctx_boxed_972_; size_t v_res_973_; lean_object* v_r_974_; 
v_ctx_boxed_972_ = lean_unbox_usize(v_ctx_968_);
lean_dec(v_ctx_968_);
v_res_973_ = lean_llvm_create_string_attribute(v_ctx_boxed_972_, v_key_969_, v_value_970_);
v_r_974_ = lean_box_usize(v_res_973_);
return v_r_974_;
}
}
LEAN_EXPORT lean_object* l_LLVM_addAttributeAtIndex___boxed(lean_object* v_ctx_980_, lean_object* v_fn_981_, lean_object* v_idx_982_, lean_object* v_attr_983_, lean_object* v_a_00___x40___internal___hyg_984_){
_start:
{
size_t v_ctx_boxed_985_; size_t v_fn_boxed_986_; uint64_t v_idx_boxed_987_; size_t v_attr_boxed_988_; lean_object* v_res_989_; 
v_ctx_boxed_985_ = lean_unbox_usize(v_ctx_980_);
lean_dec(v_ctx_980_);
v_fn_boxed_986_ = lean_unbox_usize(v_fn_981_);
lean_dec(v_fn_981_);
v_idx_boxed_987_ = lean_unbox_uint64(v_idx_982_);
lean_dec_ref(v_idx_982_);
v_attr_boxed_988_ = lean_unbox_usize(v_attr_983_);
lean_dec(v_attr_983_);
v_res_989_ = lean_llvm_add_attribute_at_index(v_ctx_boxed_985_, v_fn_boxed_986_, v_idx_boxed_987_, v_attr_boxed_988_);
return v_res_989_;
}
}
static uint64_t _init_l_LLVM_Visibility_default(void){
_start:
{
uint64_t v___x_990_; 
v___x_990_ = 0ULL;
return v___x_990_;
}
}
static uint64_t _init_l_LLVM_Visibility_hidden(void){
_start:
{
uint64_t v___x_991_; 
v___x_991_ = 1ULL;
return v___x_991_;
}
}
static uint64_t _init_l_LLVM_Visibility_protected(void){
_start:
{
uint64_t v___x_992_; 
v___x_992_ = 2ULL;
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setVisibility___boxed(lean_object* v_ctx_997_, lean_object* v_value_998_, lean_object* v_visibility_999_, lean_object* v_a_00___x40___internal___hyg_1000_){
_start:
{
size_t v_ctx_boxed_1001_; size_t v_value_boxed_1002_; uint64_t v_visibility_boxed_1003_; lean_object* v_res_1004_; 
v_ctx_boxed_1001_ = lean_unbox_usize(v_ctx_997_);
lean_dec(v_ctx_997_);
v_value_boxed_1002_ = lean_unbox_usize(v_value_998_);
lean_dec(v_value_998_);
v_visibility_boxed_1003_ = lean_unbox_uint64(v_visibility_999_);
lean_dec_ref(v_visibility_999_);
v_res_1004_ = lean_llvm_set_visibility(v_ctx_boxed_1001_, v_value_boxed_1002_, v_visibility_boxed_1003_);
return v_res_1004_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_default(void){
_start:
{
uint64_t v___x_1005_; 
v___x_1005_ = 0ULL;
return v___x_1005_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_import(void){
_start:
{
uint64_t v___x_1006_; 
v___x_1006_ = 1ULL;
return v___x_1006_;
}
}
static uint64_t _init_l_LLVM_DLLStorageClass_export(void){
_start:
{
uint64_t v___x_1007_; 
v___x_1007_ = 2ULL;
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setDLLStorageClass___boxed(lean_object* v_ctx_1012_, lean_object* v_value_1013_, lean_object* v_dllStorageClass_1014_, lean_object* v_a_00___x40___internal___hyg_1015_){
_start:
{
size_t v_ctx_boxed_1016_; size_t v_value_boxed_1017_; uint64_t v_dllStorageClass_boxed_1018_; lean_object* v_res_1019_; 
v_ctx_boxed_1016_ = lean_unbox_usize(v_ctx_1012_);
lean_dec(v_ctx_1012_);
v_value_boxed_1017_ = lean_unbox_usize(v_value_1013_);
lean_dec(v_value_1013_);
v_dllStorageClass_boxed_1018_ = lean_unbox_uint64(v_dllStorageClass_1014_);
lean_dec_ref(v_dllStorageClass_1014_);
v_res_1019_ = lean_llvm_set_dll_storage_class(v_ctx_boxed_1016_, v_value_boxed_1017_, v_dllStorageClass_boxed_1018_);
return v_res_1019_;
}
}
static uint64_t _init_l_LLVM_Linkage_external(void){
_start:
{
uint64_t v___x_1020_; 
v___x_1020_ = 0ULL;
return v___x_1020_;
}
}
static uint64_t _init_l_LLVM_Linkage_availableExternally(void){
_start:
{
uint64_t v___x_1021_; 
v___x_1021_ = 1ULL;
return v___x_1021_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceAny(void){
_start:
{
uint64_t v___x_1022_; 
v___x_1022_ = 2ULL;
return v___x_1022_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceODR(void){
_start:
{
uint64_t v___x_1023_; 
v___x_1023_ = 3ULL;
return v___x_1023_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkOnceODRAutoHide(void){
_start:
{
uint64_t v___x_1024_; 
v___x_1024_ = 4ULL;
return v___x_1024_;
}
}
static uint64_t _init_l_LLVM_Linkage_weakAny(void){
_start:
{
uint64_t v___x_1025_; 
v___x_1025_ = 5ULL;
return v___x_1025_;
}
}
static uint64_t _init_l_LLVM_Linkage_weakODR(void){
_start:
{
uint64_t v___x_1026_; 
v___x_1026_ = 6ULL;
return v___x_1026_;
}
}
static uint64_t _init_l_LLVM_Linkage_appending(void){
_start:
{
uint64_t v___x_1027_; 
v___x_1027_ = 7ULL;
return v___x_1027_;
}
}
static uint64_t _init_l_LLVM_Linkage_internal(void){
_start:
{
uint64_t v___x_1028_; 
v___x_1028_ = 8ULL;
return v___x_1028_;
}
}
static uint64_t _init_l_LLVM_Linkage_private(void){
_start:
{
uint64_t v___x_1029_; 
v___x_1029_ = 9ULL;
return v___x_1029_;
}
}
static uint64_t _init_l_LLVM_Linkage_dllImport(void){
_start:
{
uint64_t v___x_1030_; 
v___x_1030_ = 10ULL;
return v___x_1030_;
}
}
static uint64_t _init_l_LLVM_Linkage_dllExport(void){
_start:
{
uint64_t v___x_1031_; 
v___x_1031_ = 11ULL;
return v___x_1031_;
}
}
static uint64_t _init_l_LLVM_Linkage_externalWeak(void){
_start:
{
uint64_t v___x_1032_; 
v___x_1032_ = 12ULL;
return v___x_1032_;
}
}
static uint64_t _init_l_LLVM_Linkage_ghost(void){
_start:
{
uint64_t v___x_1033_; 
v___x_1033_ = 13ULL;
return v___x_1033_;
}
}
static uint64_t _init_l_LLVM_Linkage_common(void){
_start:
{
uint64_t v___x_1034_; 
v___x_1034_ = 14ULL;
return v___x_1034_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkerPrivate(void){
_start:
{
uint64_t v___x_1035_; 
v___x_1035_ = 15ULL;
return v___x_1035_;
}
}
static uint64_t _init_l_LLVM_Linkage_linkerPrivateWeak(void){
_start:
{
uint64_t v___x_1036_; 
v___x_1036_ = 16ULL;
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_LLVM_setLinkage___boxed(lean_object* v_ctx_1041_, lean_object* v_value_1042_, lean_object* v_linkage_1043_, lean_object* v_a_00___x40___internal___hyg_1044_){
_start:
{
size_t v_ctx_boxed_1045_; size_t v_value_boxed_1046_; uint64_t v_linkage_boxed_1047_; lean_object* v_res_1048_; 
v_ctx_boxed_1045_ = lean_unbox_usize(v_ctx_1041_);
lean_dec(v_ctx_1041_);
v_value_boxed_1046_ = lean_unbox_usize(v_value_1042_);
lean_dec(v_value_1042_);
v_linkage_boxed_1047_ = lean_unbox_uint64(v_linkage_1043_);
lean_dec_ref(v_linkage_1043_);
v_res_1048_ = lean_llvm_set_linkage(v_ctx_boxed_1045_, v_value_boxed_1046_, v_linkage_boxed_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT size_t l_LLVM_i1Type(size_t v_ctx_1049_){
_start:
{
uint64_t v___x_1051_; size_t v___x_1052_; 
v___x_1051_ = 1ULL;
v___x_1052_ = lean_llvm_int_type_in_context(v_ctx_1049_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i1Type___boxed(lean_object* v_ctx_1053_, lean_object* v_a_1054_){
_start:
{
size_t v_ctx_boxed_1055_; size_t v_res_1056_; lean_object* v_r_1057_; 
v_ctx_boxed_1055_ = lean_unbox_usize(v_ctx_1053_);
lean_dec(v_ctx_1053_);
v_res_1056_ = l_LLVM_i1Type(v_ctx_boxed_1055_);
v_r_1057_ = lean_box_usize(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT size_t l_LLVM_i8Type(size_t v_ctx_1058_){
_start:
{
uint64_t v___x_1060_; size_t v___x_1061_; 
v___x_1060_ = 8ULL;
v___x_1061_ = lean_llvm_int_type_in_context(v_ctx_1058_, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8Type___boxed(lean_object* v_ctx_1062_, lean_object* v_a_1063_){
_start:
{
size_t v_ctx_boxed_1064_; size_t v_res_1065_; lean_object* v_r_1066_; 
v_ctx_boxed_1064_ = lean_unbox_usize(v_ctx_1062_);
lean_dec(v_ctx_1062_);
v_res_1065_ = l_LLVM_i8Type(v_ctx_boxed_1064_);
v_r_1066_ = lean_box_usize(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT size_t l_LLVM_i16Type(size_t v_ctx_1067_){
_start:
{
uint64_t v___x_1069_; size_t v___x_1070_; 
v___x_1069_ = 16ULL;
v___x_1070_ = lean_llvm_int_type_in_context(v_ctx_1067_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i16Type___boxed(lean_object* v_ctx_1071_, lean_object* v_a_1072_){
_start:
{
size_t v_ctx_boxed_1073_; size_t v_res_1074_; lean_object* v_r_1075_; 
v_ctx_boxed_1073_ = lean_unbox_usize(v_ctx_1071_);
lean_dec(v_ctx_1071_);
v_res_1074_ = l_LLVM_i16Type(v_ctx_boxed_1073_);
v_r_1075_ = lean_box_usize(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT size_t l_LLVM_i32Type(size_t v_ctx_1076_){
_start:
{
uint64_t v___x_1078_; size_t v___x_1079_; 
v___x_1078_ = 32ULL;
v___x_1079_ = lean_llvm_int_type_in_context(v_ctx_1076_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i32Type___boxed(lean_object* v_ctx_1080_, lean_object* v_a_1081_){
_start:
{
size_t v_ctx_boxed_1082_; size_t v_res_1083_; lean_object* v_r_1084_; 
v_ctx_boxed_1082_ = lean_unbox_usize(v_ctx_1080_);
lean_dec(v_ctx_1080_);
v_res_1083_ = l_LLVM_i32Type(v_ctx_boxed_1082_);
v_r_1084_ = lean_box_usize(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT size_t l_LLVM_i64Type(size_t v_ctx_1085_){
_start:
{
uint64_t v___x_1087_; size_t v___x_1088_; 
v___x_1087_ = 64ULL;
v___x_1088_ = lean_llvm_int_type_in_context(v_ctx_1085_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i64Type___boxed(lean_object* v_ctx_1089_, lean_object* v_a_1090_){
_start:
{
size_t v_ctx_boxed_1091_; size_t v_res_1092_; lean_object* v_r_1093_; 
v_ctx_boxed_1091_ = lean_unbox_usize(v_ctx_1089_);
lean_dec(v_ctx_1089_);
v_res_1092_ = l_LLVM_i64Type(v_ctx_boxed_1091_);
v_r_1093_ = lean_box_usize(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT size_t l_LLVM_voidPtrType(size_t v_ctx_1094_){
_start:
{
uint64_t v___x_1096_; size_t v___x_1097_; size_t v___x_1098_; 
v___x_1096_ = 8ULL;
v___x_1097_ = lean_llvm_int_type_in_context(v_ctx_1094_, v___x_1096_);
v___x_1098_ = lean_llvm_pointer_type(v_ctx_1094_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_LLVM_voidPtrType___boxed(lean_object* v_ctx_1099_, lean_object* v_a_1100_){
_start:
{
size_t v_ctx_boxed_1101_; size_t v_res_1102_; lean_object* v_r_1103_; 
v_ctx_boxed_1101_ = lean_unbox_usize(v_ctx_1099_);
lean_dec(v_ctx_1099_);
v_res_1102_ = l_LLVM_voidPtrType(v_ctx_boxed_1101_);
v_r_1103_ = lean_box_usize(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT size_t l_LLVM_i8PtrType(size_t v_ctx_1104_){
_start:
{
size_t v___x_1106_; 
v___x_1106_ = l_LLVM_voidPtrType(v_ctx_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8PtrType___boxed(lean_object* v_ctx_1107_, lean_object* v_a_1108_){
_start:
{
size_t v_ctx_boxed_1109_; size_t v_res_1110_; lean_object* v_r_1111_; 
v_ctx_boxed_1109_ = lean_unbox_usize(v_ctx_1107_);
lean_dec(v_ctx_1107_);
v_res_1110_ = l_LLVM_i8PtrType(v_ctx_boxed_1109_);
v_r_1111_ = lean_box_usize(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT size_t l_LLVM_constTrue(size_t v_ctx_1112_){
_start:
{
size_t v___x_1114_; uint64_t v___x_1115_; uint8_t v___x_1116_; size_t v___x_1117_; 
v___x_1114_ = l_LLVM_i1Type(v_ctx_1112_);
v___x_1115_ = 1ULL;
v___x_1116_ = 0;
v___x_1117_ = lean_llvm_const_int(v_ctx_1112_, v___x_1114_, v___x_1115_, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constTrue___boxed(lean_object* v_ctx_1118_, lean_object* v_a_1119_){
_start:
{
size_t v_ctx_boxed_1120_; size_t v_res_1121_; lean_object* v_r_1122_; 
v_ctx_boxed_1120_ = lean_unbox_usize(v_ctx_1118_);
lean_dec(v_ctx_1118_);
v_res_1121_ = l_LLVM_constTrue(v_ctx_boxed_1120_);
v_r_1122_ = lean_box_usize(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT size_t l_LLVM_constFalse(size_t v_ctx_1123_){
_start:
{
size_t v___x_1125_; uint64_t v___x_1126_; uint8_t v___x_1127_; size_t v___x_1128_; 
v___x_1125_ = l_LLVM_i1Type(v_ctx_1123_);
v___x_1126_ = 0ULL;
v___x_1127_ = 0;
v___x_1128_ = lean_llvm_const_int(v_ctx_1123_, v___x_1125_, v___x_1126_, v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constFalse___boxed(lean_object* v_ctx_1129_, lean_object* v_a_1130_){
_start:
{
size_t v_ctx_boxed_1131_; size_t v_res_1132_; lean_object* v_r_1133_; 
v_ctx_boxed_1131_ = lean_unbox_usize(v_ctx_1129_);
lean_dec(v_ctx_1129_);
v_res_1132_ = l_LLVM_constFalse(v_ctx_boxed_1131_);
v_r_1133_ = lean_box_usize(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt_x27(size_t v_ctx_1134_, uint64_t v_width_1135_, uint64_t v_value_1136_, uint8_t v_signExtend_1137_){
_start:
{
size_t v___x_1139_; size_t v___x_1140_; 
v___x_1139_ = lean_llvm_int_type_in_context(v_ctx_1134_, v_width_1135_);
v___x_1140_ = lean_llvm_const_int(v_ctx_1134_, v___x_1139_, v_value_1136_, v_signExtend_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt_x27___boxed(lean_object* v_ctx_1141_, lean_object* v_width_1142_, lean_object* v_value_1143_, lean_object* v_signExtend_1144_, lean_object* v_a_1145_){
_start:
{
size_t v_ctx_boxed_1146_; uint64_t v_width_boxed_1147_; uint64_t v_value_boxed_1148_; uint8_t v_signExtend_boxed_1149_; size_t v_res_1150_; lean_object* v_r_1151_; 
v_ctx_boxed_1146_ = lean_unbox_usize(v_ctx_1141_);
lean_dec(v_ctx_1141_);
v_width_boxed_1147_ = lean_unbox_uint64(v_width_1142_);
lean_dec_ref(v_width_1142_);
v_value_boxed_1148_ = lean_unbox_uint64(v_value_1143_);
lean_dec_ref(v_value_1143_);
v_signExtend_boxed_1149_ = lean_unbox(v_signExtend_1144_);
v_res_1150_ = l_LLVM_constInt_x27(v_ctx_boxed_1146_, v_width_boxed_1147_, v_value_boxed_1148_, v_signExtend_boxed_1149_);
v_r_1151_ = lean_box_usize(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt1(size_t v_ctx_1152_, uint64_t v_value_1153_, uint8_t v_signExtend_1154_){
_start:
{
uint64_t v___x_1156_; size_t v___x_1157_; 
v___x_1156_ = 1ULL;
v___x_1157_ = l_LLVM_constInt_x27(v_ctx_1152_, v___x_1156_, v_value_1153_, v_signExtend_1154_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt1___boxed(lean_object* v_ctx_1158_, lean_object* v_value_1159_, lean_object* v_signExtend_1160_, lean_object* v_a_1161_){
_start:
{
size_t v_ctx_boxed_1162_; uint64_t v_value_boxed_1163_; uint8_t v_signExtend_boxed_1164_; size_t v_res_1165_; lean_object* v_r_1166_; 
v_ctx_boxed_1162_ = lean_unbox_usize(v_ctx_1158_);
lean_dec(v_ctx_1158_);
v_value_boxed_1163_ = lean_unbox_uint64(v_value_1159_);
lean_dec_ref(v_value_1159_);
v_signExtend_boxed_1164_ = lean_unbox(v_signExtend_1160_);
v_res_1165_ = l_LLVM_constInt1(v_ctx_boxed_1162_, v_value_boxed_1163_, v_signExtend_boxed_1164_);
v_r_1166_ = lean_box_usize(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt8(size_t v_ctx_1167_, uint64_t v_value_1168_, uint8_t v_signExtend_1169_){
_start:
{
uint64_t v___x_1171_; size_t v___x_1172_; 
v___x_1171_ = 8ULL;
v___x_1172_ = l_LLVM_constInt_x27(v_ctx_1167_, v___x_1171_, v_value_1168_, v_signExtend_1169_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt8___boxed(lean_object* v_ctx_1173_, lean_object* v_value_1174_, lean_object* v_signExtend_1175_, lean_object* v_a_1176_){
_start:
{
size_t v_ctx_boxed_1177_; uint64_t v_value_boxed_1178_; uint8_t v_signExtend_boxed_1179_; size_t v_res_1180_; lean_object* v_r_1181_; 
v_ctx_boxed_1177_ = lean_unbox_usize(v_ctx_1173_);
lean_dec(v_ctx_1173_);
v_value_boxed_1178_ = lean_unbox_uint64(v_value_1174_);
lean_dec_ref(v_value_1174_);
v_signExtend_boxed_1179_ = lean_unbox(v_signExtend_1175_);
v_res_1180_ = l_LLVM_constInt8(v_ctx_boxed_1177_, v_value_boxed_1178_, v_signExtend_boxed_1179_);
v_r_1181_ = lean_box_usize(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt32(size_t v_ctx_1182_, uint64_t v_value_1183_, uint8_t v_signExtend_1184_){
_start:
{
uint64_t v___x_1186_; size_t v___x_1187_; 
v___x_1186_ = 32ULL;
v___x_1187_ = l_LLVM_constInt_x27(v_ctx_1182_, v___x_1186_, v_value_1183_, v_signExtend_1184_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt32___boxed(lean_object* v_ctx_1188_, lean_object* v_value_1189_, lean_object* v_signExtend_1190_, lean_object* v_a_1191_){
_start:
{
size_t v_ctx_boxed_1192_; uint64_t v_value_boxed_1193_; uint8_t v_signExtend_boxed_1194_; size_t v_res_1195_; lean_object* v_r_1196_; 
v_ctx_boxed_1192_ = lean_unbox_usize(v_ctx_1188_);
lean_dec(v_ctx_1188_);
v_value_boxed_1193_ = lean_unbox_uint64(v_value_1189_);
lean_dec_ref(v_value_1189_);
v_signExtend_boxed_1194_ = lean_unbox(v_signExtend_1190_);
v_res_1195_ = l_LLVM_constInt32(v_ctx_boxed_1192_, v_value_boxed_1193_, v_signExtend_boxed_1194_);
v_r_1196_ = lean_box_usize(v_res_1195_);
return v_r_1196_;
}
}
LEAN_EXPORT size_t l_LLVM_constInt64(size_t v_ctx_1197_, uint64_t v_value_1198_, uint8_t v_signExtend_1199_){
_start:
{
uint64_t v___x_1201_; size_t v___x_1202_; 
v___x_1201_ = 64ULL;
v___x_1202_ = l_LLVM_constInt_x27(v_ctx_1197_, v___x_1201_, v_value_1198_, v_signExtend_1199_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt64___boxed(lean_object* v_ctx_1203_, lean_object* v_value_1204_, lean_object* v_signExtend_1205_, lean_object* v_a_1206_){
_start:
{
size_t v_ctx_boxed_1207_; uint64_t v_value_boxed_1208_; uint8_t v_signExtend_boxed_1209_; size_t v_res_1210_; lean_object* v_r_1211_; 
v_ctx_boxed_1207_ = lean_unbox_usize(v_ctx_1203_);
lean_dec(v_ctx_1203_);
v_value_boxed_1208_ = lean_unbox_uint64(v_value_1204_);
lean_dec_ref(v_value_1204_);
v_signExtend_boxed_1209_ = lean_unbox(v_signExtend_1205_);
v_res_1210_ = l_LLVM_constInt64(v_ctx_boxed_1207_, v_value_boxed_1208_, v_signExtend_boxed_1209_);
v_r_1211_ = lean_box_usize(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT size_t l_LLVM_constIntSizeT(size_t v_ctx_1212_, uint64_t v_value_1213_, uint8_t v_signExtend_1214_){
_start:
{
uint64_t v___x_1216_; size_t v___x_1217_; 
v___x_1216_ = 64ULL;
v___x_1217_ = l_LLVM_constInt_x27(v_ctx_1212_, v___x_1216_, v_value_1213_, v_signExtend_1214_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntSizeT___boxed(lean_object* v_ctx_1218_, lean_object* v_value_1219_, lean_object* v_signExtend_1220_, lean_object* v_a_1221_){
_start:
{
size_t v_ctx_boxed_1222_; uint64_t v_value_boxed_1223_; uint8_t v_signExtend_boxed_1224_; size_t v_res_1225_; lean_object* v_r_1226_; 
v_ctx_boxed_1222_ = lean_unbox_usize(v_ctx_1218_);
lean_dec(v_ctx_1218_);
v_value_boxed_1223_ = lean_unbox_uint64(v_value_1219_);
lean_dec_ref(v_value_1219_);
v_signExtend_boxed_1224_ = lean_unbox(v_signExtend_1220_);
v_res_1225_ = l_LLVM_constIntSizeT(v_ctx_boxed_1222_, v_value_boxed_1223_, v_signExtend_boxed_1224_);
v_r_1226_ = lean_box_usize(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT size_t l_LLVM_constIntUnsigned(size_t v_ctx_1227_, uint64_t v_value_1228_, uint8_t v_signExtend_1229_){
_start:
{
uint64_t v___x_1231_; size_t v___x_1232_; 
v___x_1231_ = 32ULL;
v___x_1232_ = l_LLVM_constInt_x27(v_ctx_1227_, v___x_1231_, v_value_1228_, v_signExtend_1229_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned___boxed(lean_object* v_ctx_1233_, lean_object* v_value_1234_, lean_object* v_signExtend_1235_, lean_object* v_a_1236_){
_start:
{
size_t v_ctx_boxed_1237_; uint64_t v_value_boxed_1238_; uint8_t v_signExtend_boxed_1239_; size_t v_res_1240_; lean_object* v_r_1241_; 
v_ctx_boxed_1237_ = lean_unbox_usize(v_ctx_1233_);
lean_dec(v_ctx_1233_);
v_value_boxed_1238_ = lean_unbox_uint64(v_value_1234_);
lean_dec_ref(v_value_1234_);
v_signExtend_boxed_1239_ = lean_unbox(v_signExtend_1235_);
v_res_1240_ = l_LLVM_constIntUnsigned(v_ctx_boxed_1237_, v_value_boxed_1238_, v_signExtend_boxed_1239_);
v_r_1241_ = lean_box_usize(v_res_1240_);
return v_r_1241_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_LLVMBindings(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_LLVMBindings(builtin);
}
#ifdef __cplusplus
}
#endif
