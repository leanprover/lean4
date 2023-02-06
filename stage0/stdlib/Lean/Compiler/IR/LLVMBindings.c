// Lean compiler output
// Module: Lean.Compiler.IR.LLVMBindings
// Imports: Init
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
LEAN_EXPORT lean_object* l_LLVM_buildSext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_type_of(size_t, size_t, lean_object*);
lean_object* lean_llvm_function_type(size_t, size_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constFalse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i16Type(size_t, lean_object*);
lean_object* lean_llvm_add_case(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i8Type___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_append_basic_block_in_context(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_linkModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_addCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_llvmInitializeTargetInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LLVM_addFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt64___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_insert_block(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_moduleToString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_addGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_print_module_to_string(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt1(size_t, uint64_t, uint8_t, lean_object*);
lean_object* lean_llvm_build_sext_or_trunc(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_build_switch(size_t, size_t, size_t, size_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildUnreachable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createTargetMachine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_const_int(size_t, size_t, uint64_t, uint8_t, lean_object*);
lean_object* lean_llvm_set_tail_call(size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSextOrTrunc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i8Type(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildPtrToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt64(size_t, uint64_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i1Type___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_write_bitcode_to_file(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_runPassManager___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getOrAddGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_zext(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_build_ptr_to_int(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createContext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constTrue___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_module_to_string(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_positionBuilderAtEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildLoad2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_call2(size_t, size_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getDefaultTargetTriple___boxed(lean_object*);
lean_object* lean_llvm_get_target_from_triple(size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_functionType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_PassManagerBuilder_setOptLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_const_array(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_get_named_global(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_countParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_setTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt_x27(size_t, uint64_t, uint64_t, uint8_t, lean_object*);
lean_object* lean_llvm_build_mul(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_build_unreachable(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i16Type___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_PassManagerBuilder_populateModulePassManager___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt8(size_t, uint64_t, uint8_t, lean_object*);
lean_object* llvm_get_param(size_t, size_t, uint64_t, lean_object*);
lean_object* lean_llvm_build_global_string(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createBuilderInContext___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_array_type(size_t, size_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildCondBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getOrAddFunction(size_t, size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildStore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_dispose_pass_manager_builder(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt32(size_t, uint64_t, uint8_t, lean_object*);
lean_object* lean_llvm_initialize_target_info(lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getInsertBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_get_undef(size_t, size_t, lean_object*);
lean_object* lean_llvm_create_context(lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildInBoundsGEP2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getOrAddFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_voidType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_CodegenFileType_ObjectFile;
lean_object* lean_llvm_create_pass_manager(size_t, lean_object*);
lean_object* lean_llvm_parse_bitcode(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_clearInsertionPosition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_create_builder_in_context(size_t, lean_object*);
lean_object* lean_llvm_build_cond_br(size_t, size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_printModuletoString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_ret(size_t, size_t, size_t, lean_object*);
lean_object* lean_llvm_pass_manager_builder_populate_module_pass_manager(size_t, size_t, size_t, lean_object*);
lean_object* lean_llvm_target_machine_emit_to_file(size_t, size_t, size_t, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_parseBitcode___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_inbounds_gep2(size_t, size_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildGEP2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i32Type___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_add_global(size_t, size_t, lean_object*, size_t, lean_object*);
lean_object* lean_llvm_build_gep2(size_t, size_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t llvm_count_params(size_t, size_t);
LEAN_EXPORT lean_object* l_LLVM_buildGlobalString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constFalse(size_t, lean_object*);
lean_object* lean_llvm_build_br(size_t, size_t, size_t, lean_object*);
lean_object* lean_llvm_opaque_pointer_type_in_context(size_t, uint64_t, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_NE;
lean_object* lean_llvm_dispose_target_machine(size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_UGT;
lean_object* lean_llvm_position_builder_at_end(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_llvm_build_not(size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_const_pointer_null(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_arrayType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildZext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i8PtrType(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getUndef___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_disposePassManager___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_create_memory_buffer_with_contents_of_file(size_t, lean_object*, lean_object*);
lean_object* lean_llvm_run_pass_manager(size_t, size_t, size_t, lean_object*);
lean_object* lean_llvm_float_type_in_context(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createMemoryBufferWithContentsOfFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_set_initializer(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildBr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_disposeModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildCall2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_IntPredicate_EQ;
lean_object* lean_llvm_build_add(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getOrAddGlobal(size_t, size_t, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_voidPtrType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_intTypeInContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_create_module(size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_pointerType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_sub(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_get_named_function(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_setInitializer___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i32Type(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned(size_t, uint64_t, uint8_t, lean_object*);
lean_object* lean_llvm_clear_insertion_position(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_double_type_in_context(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_store(size_t, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_appendBasicBlockInContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_disposePassManagerBuilder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constPointerNull___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_dispose_module(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSub___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getTargetFromTriple___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getNamedFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constString___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_pointer_type(size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_LLVM_CodegenFileType_AssemblyFile;
lean_object* lean_llvm_build_icmp(size_t, size_t, uint64_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getNamedGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_alloca(size_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_writeBitcodeToFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createPassManagerBuilder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i8PtrType___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_create_pass_manager_builder(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_opaquePointerTypeInContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_doubleTypeInContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildSwitch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_typeOf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_printModuletoFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i1Type(size_t, lean_object*);
lean_object* lean_llvm_get_basic_block_parent(size_t, size_t, lean_object*);
lean_object* lean_llvm_get_default_target_triple(lean_object*);
lean_object* lean_llvm_const_string(size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_targetMachineEmitToFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_void_type_in_context(size_t, lean_object*);
lean_object* lean_llvm_pass_manager_builder_set_opt_level(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildAlloca___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_getBasicBlockParent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_createPassManager___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_dispose_pass_manager(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i64Type(size_t, lean_object*);
lean_object* lean_llvm_print_module_to_file(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_voidPtrType(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_disposeTargetMachine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_build_sext(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_add_function(size_t, size_t, lean_object*, size_t, lean_object*);
lean_object* lean_llvm_link_modules(size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constTrue(size_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildRet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_i64Type___boxed(lean_object*, lean_object*);
lean_object* lean_llvm_build_load2(size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_llvm_int_type_in_context(size_t, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_constInt1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_llvm_create_target_machine(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_floatTypeInContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LLVM_buildICmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l_LLVM_CodegenFileType_AssemblyFile() {
_start:
{
uint64_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint64_t _init_l_LLVM_CodegenFileType_ObjectFile() {
_start:
{
uint64_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint64_t _init_l_LLVM_IntPredicate_EQ() {
_start:
{
uint64_t x_1; 
x_1 = 32;
return x_1;
}
}
static uint64_t _init_l_LLVM_IntPredicate_NE() {
_start:
{
uint64_t x_1; 
x_1 = 33;
return x_1;
}
}
static uint64_t _init_l_LLVM_IntPredicate_UGT() {
_start:
{
uint64_t x_1; 
x_1 = 34;
return x_1;
}
}
LEAN_EXPORT lean_object* l_LLVM_llvmInitializeTargetInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_llvm_initialize_target_info(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LLVM_createContext___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_llvm_create_context(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LLVM_createModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_llvm_create_module(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LLVM_moduleToString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_module_to_string(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_writeBitcodeToFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_write_bitcode_to_file(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_addFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_llvm_add_function(x_6, x_7, x_3, x_8, x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNamedFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_get_named_function(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_addGlobal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_llvm_add_global(x_6, x_7, x_3, x_8, x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_getNamedGlobal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_get_named_global(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildGlobalString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_llvm_build_global_string(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_setInitializer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_set_initializer(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_functionType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_llvm_function_type(x_6, x_7, x_3, x_8, x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_voidType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_void_type_in_context(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_intTypeInContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = lean_llvm_int_type_in_context(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_opaquePointerTypeInContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = lean_llvm_opaque_pointer_type_in_context(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_floatTypeInContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_float_type_in_context(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_doubleTypeInContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_double_type_in_context(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_pointerType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_pointer_type(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_arrayType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = lean_llvm_array_type(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_constArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_const_array(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_constString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_llvm_const_string(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LLVM_constPointerNull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_const_pointer_null(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_getUndef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_get_undef(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_createBuilderInContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_create_builder_in_context(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_appendBasicBlockInContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_append_basic_block_in_context(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_positionBuilderAtEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_llvm_position_builder_at_end(x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCall2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_llvm_build_call2(x_8, x_9, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LLVM_setTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_llvm_set_tail_call(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildCondBr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_llvm_build_cond_br(x_7, x_8, x_9, x_10, x_11, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildBr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_build_br(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAlloca___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_llvm_build_alloca(x_6, x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildLoad2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_load2(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildStore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_llvm_build_store(x_6, x_7, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildRet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_build_ret(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_build_unreachable(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildGEP2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_llvm_build_gep2(x_8, x_9, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildInBoundsGEP2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_llvm_build_inbounds_gep2(x_8, x_9, x_10, x_11, x_5, x_6, x_7);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_sext(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildZext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_zext(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSextOrTrunc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_sext_or_trunc(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSwitch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; uint64_t x_11; lean_object* x_12; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_12 = lean_llvm_build_switch(x_7, x_8, x_9, x_10, x_11, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildPtrToInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_ptr_to_int(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_mul(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_add(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_llvm_build_sub(x_7, x_8, x_9, x_10, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildNot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_llvm_build_not(x_6, x_7, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_buildICmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_llvm_build_icmp(x_8, x_9, x_10, x_11, x_12, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_LLVM_addCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_llvm_add_case(x_6, x_7, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_LLVM_getInsertBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_llvm_get_insert_block(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_clearInsertionPosition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_llvm_clear_insertion_position(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_getBasicBlockParent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_get_basic_block_parent(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_typeOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_type_of(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_llvm_const_int(x_6, x_7, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_print_module_to_string(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_printModuletoFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_llvm_print_module_to_file(x_5, x_6, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_LLVM_countParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = llvm_count_params(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_getParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = llvm_get_param(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_createMemoryBufferWithContentsOfFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_llvm_create_memory_buffer_with_contents_of_file(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LLVM_parseBitcode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_parse_bitcode(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_linkModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_link_modules(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_getDefaultTargetTriple___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_llvm_get_default_target_triple(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LLVM_getTargetFromTriple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_llvm_get_target_from_triple(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LLVM_createTargetMachine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_llvm_create_target_machine(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_targetMachineEmitToFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_11 = lean_llvm_target_machine_emit_to_file(x_7, x_8, x_9, x_4, x_10, x_6);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_LLVM_createPassManager___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_create_pass_manager(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposePassManager___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_dispose_pass_manager(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_runPassManager___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_run_pass_manager(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_createPassManagerBuilder___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_llvm_create_pass_manager_builder(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposePassManagerBuilder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_dispose_pass_manager_builder(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_PassManagerBuilder_setOptLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_pass_manager_builder_set_opt_level(x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_PassManagerBuilder_populateModulePassManager___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_llvm_pass_manager_builder_populate_module_pass_manager(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeTargetMachine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_dispose_target_machine(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_disposeModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_llvm_dispose_module(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_getOrAddFunction(size_t x_1, size_t x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_llvm_get_named_function(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_llvm_add_function(x_1, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_getOrAddFunction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_LLVM_getOrAddFunction(x_6, x_7, x_3, x_8, x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_getOrAddGlobal(size_t x_1, size_t x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_llvm_get_named_global(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_llvm_add_global(x_1, x_2, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_getOrAddGlobal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_LLVM_getOrAddGlobal(x_6, x_7, x_3, x_8, x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_LLVM_i1Type(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i1Type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i1Type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8Type(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 8;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8Type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i8Type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i16Type(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 16;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i16Type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i16Type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i32Type(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 32;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i32Type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i32Type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i64Type(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 64;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i64Type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i64Type(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_voidPtrType(size_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = 8;
x_4 = lean_llvm_int_type_in_context(x_1, x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_llvm_pointer_type(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_voidPtrType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_voidPtrType(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8PtrType(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LLVM_voidPtrType(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LLVM_i8PtrType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_i8PtrType(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_constTrue(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LLVM_i1Type(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = 1;
x_7 = 0;
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_llvm_const_int(x_1, x_8, x_6, x_7, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_constTrue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_constTrue(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_constFalse(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LLVM_i1Type(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; size_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = 0;
x_7 = 0;
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_llvm_const_int(x_1, x_8, x_6, x_7, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_constFalse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_LLVM_constFalse(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt_x27(size_t x_1, uint64_t x_2, uint64_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_llvm_int_type_in_context(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_10 = lean_llvm_const_int(x_1, x_9, x_3, x_4, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; uint64_t x_7; uint64_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_LLVM_constInt_x27(x_6, x_7, x_8, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt1(size_t x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_LLVM_constInt_x27(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_LLVM_constInt1(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt8(size_t x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = 8;
x_6 = l_LLVM_constInt_x27(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_LLVM_constInt8(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt32(size_t x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = 32;
x_6 = l_LLVM_constInt_x27(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_LLVM_constInt32(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt64(size_t x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = 64;
x_6 = l_LLVM_constInt_x27(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constInt64___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_LLVM_constInt64(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned(size_t x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = 64;
x_6 = l_LLVM_constInt_x27(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LLVM_constIntUnsigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint64_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_LLVM_constIntUnsigned(x_5, x_6, x_7, x_4);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LLVM_CodegenFileType_AssemblyFile = _init_l_LLVM_CodegenFileType_AssemblyFile();
l_LLVM_CodegenFileType_ObjectFile = _init_l_LLVM_CodegenFileType_ObjectFile();
l_LLVM_IntPredicate_EQ = _init_l_LLVM_IntPredicate_EQ();
l_LLVM_IntPredicate_NE = _init_l_LLVM_IntPredicate_NE();
l_LLVM_IntPredicate_UGT = _init_l_LLVM_IntPredicate_UGT();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
