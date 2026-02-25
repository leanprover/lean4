// Lean compiler output
// Module: LeanChecker.Replay
// Imports: public import Lean.CoreM public import Lean.AddDecl public import Lean.Util.FoldConsts
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__0 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__0_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':\n"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__1 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__1_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__2 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__3 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__3_value;
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__6 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__6_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Environment.Replay'.replayConstant"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__5 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__5_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LeanChecker.Replay"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__4 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__4_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Environment_Replay_x27_replayConstant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__7;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "No such constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Invalid constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "No such recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_take(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_11);
x_14 = l_Lean_NameSet_insert(x_12, x_1);
lean_ctor_set(x_9, 2, x_14);
lean_ctor_set(x_9, 1, x_13);
x_15 = lean_st_ref_set(x_2, x_9);
x_16 = lean_box(x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 2);
x_21 = lean_ctor_get(x_9, 3);
x_22 = lean_ctor_get(x_9, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_23 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_19);
x_24 = l_Lean_NameSet_insert(x_20, x_1);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
x_26 = lean_st_ref_set(x_2, x_25);
x_27 = lean_box(x_6);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_isTodo(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Kernel_Exception_toMessageData(x_1, x_3);
x_5 = l_Lean_MessageData_toString(x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_throwKernelException(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = lean_box(0);
x_8 = lean_add_decl(x_5, x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Environment_Replay_x27_throwKernelException___redArg(x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_st_ref_take(x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
x_16 = lean_st_ref_set(x_2, x_13);
x_17 = lean_box(0);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = lean_st_ref_set(x_2, x_22);
x_24 = lean_box(0);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_st_ref_take(x_2);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 4);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 5, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
x_33 = lean_st_ref_set(x_2, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_addDecl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_obj_once(&l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0, &l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once, _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0);
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = lean_box(0);
x_8 = l_instInhabitedOfMonad___redArg(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_3(x_10, x_2, x_3, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 2);
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_8);
lean_ctor_set(x_6, 2, x_9);
x_10 = lean_st_ref_set(x_4, x_6);
x_11 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_18 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_15);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
x_20 = lean_st_ref_set(x_4, x_19);
x_21 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0));
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_7, x_5);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_4(x_2, x_9, x_4, x_5, lean_box(0));
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Environment_Replay_x27_replayConstant___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_4(x_1, x_6, x_3, x_4, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_ConstantInfo_name(x_5);
x_8 = l_Lean_ConstantInfo_type(x_5);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_ConstantInfo_name(x_11);
x_14 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_name(x_7);
x_10 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(x_8, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_ConstantInfo_name(x_17);
x_20 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(x_18, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_1 = x_16;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_st_ref_take(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Lean_ConstantInfo_name(x_6);
x_13 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_12, x_10);
x_14 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_12, x_11);
lean_dec(x_12);
lean_ctor_set(x_8, 2, x_14);
lean_ctor_set(x_8, 1, x_13);
x_15 = lean_st_ref_set(x_3, x_8);
x_16 = lean_box(0);
x_1 = x_7;
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_23 = l_Lean_ConstantInfo_name(x_6);
x_24 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_23, x_19);
x_25 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_23, x_20);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_22);
x_27 = lean_st_ref_set(x_3, x_26);
x_28 = lean_box(0);
x_1 = x_7;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_instInhabitedConstantInfo_default;
x_11 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(x_10, x_3, x_8);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_instInhabitedConstantInfo_default;
x_16 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(x_15, x_3, x_13);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_1 = x_14;
x_2 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_ConstantInfo_inductiveVal_x21(x_9);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
x_14 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_12, x_13, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Lean_ConstantInfo_inductiveVal_x21(x_18);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_23 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_21, x_22, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_19;
x_2 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Environment_Replay_x27_replayConstants(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_8;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_4);
lean_inc_ref(x_3);
x_11 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_9, x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_dec_ref(x_11);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__6));
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_unsigned_to_nat(81u);
x_4 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__5));
x_5 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Environment_Replay_x27_isTodo___redArg(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_8 = lean_unbox(x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 1, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_2, x_1);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_13 = x_11;
} else {
 lean_dec_ref(x_11);
 x_13 = lean_box(0);
}
lean_inc(x_12);
x_14 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_12);
lean_inc(x_3);
lean_inc_ref(x_2);
x_15 = l_Lean_Environment_Replay_x27_replayConstants(x_14, x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_32; 
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_16 = x_15;
} else {
 lean_dec_ref(x_15);
 x_16 = lean_box(0);
}
x_17 = lean_st_ref_get(x_3);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_7;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; 
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(x_43, 0, x_1);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_44; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_12, x_3);
lean_dec_ref(x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_46, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_47;
goto block_40;
}
else
{
lean_object* x_48; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec_ref(x_45);
x_20 = x_48;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
lean_dec(x_12);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_50, x_3);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_52, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_53;
goto block_40;
}
else
{
lean_object* x_54; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
x_20 = x_54;
x_21 = lean_box(0);
goto block_31;
}
}
}
case 1:
{
uint8_t x_55; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_12, x_3);
lean_dec_ref(x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_57, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_58;
goto block_40;
}
else
{
lean_object* x_59; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec_ref(x_56);
x_20 = x_59;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_61, x_3);
lean_dec_ref(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_63, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_64;
goto block_40;
}
else
{
lean_object* x_65; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec_ref(x_62);
x_20 = x_65;
x_21 = lean_box(0);
goto block_31;
}
}
}
case 2:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_66);
x_67 = lean_st_ref_get(x_3);
x_68 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_68);
lean_dec(x_67);
lean_inc_ref(x_43);
lean_inc_ref(x_66);
x_69 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(x_69, 0, x_66);
lean_closure_set(x_69, 1, x_43);
x_73 = l_Lean_ConstantInfo_name(x_12);
lean_dec_ref(x_12);
x_74 = lean_environment_find(x_68, x_73);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 2)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_93; 
lean_dec_ref(x_74);
lean_dec_ref(x_69);
x_76 = lean_ctor_get(x_66, 0);
x_77 = lean_ctor_get(x_75, 0);
lean_inc_ref(x_77);
lean_dec_ref(x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_66, 2);
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
x_82 = lean_ctor_get(x_76, 2);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
lean_dec_ref(x_77);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 2);
lean_inc_ref(x_86);
lean_dec_ref(x_78);
x_93 = lean_name_eq(x_80, x_84);
lean_dec(x_84);
if (x_93 == 0)
{
lean_dec_ref(x_86);
x_87 = x_93;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = lean_expr_eqv(x_82, x_86);
lean_dec_ref(x_86);
x_87 = x_94;
goto block_92;
}
block_92:
{
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_7);
goto block_72;
}
else
{
uint8_t x_88; 
x_88 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_81, x_85);
lean_dec(x_85);
if (x_88 == 0)
{
lean_dec(x_83);
lean_dec(x_7);
goto block_72;
}
else
{
uint8_t x_89; 
x_89 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_79, x_83);
lean_dec(x_83);
if (x_89 == 0)
{
lean_dec(x_7);
goto block_72;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_66);
lean_dec_ref(x_43);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_7;
}
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_75);
lean_dec_ref(x_66);
lean_dec_ref(x_43);
lean_dec(x_7);
x_95 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_69, x_74, x_2, x_3);
lean_dec_ref(x_74);
x_32 = x_95;
goto block_40;
}
}
else
{
lean_object* x_96; 
lean_dec_ref(x_66);
lean_dec_ref(x_43);
lean_dec(x_7);
x_96 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_69, x_74, x_2, x_3);
lean_dec(x_74);
x_32 = x_96;
goto block_40;
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_Environment_Replay_x27_replayConstant___lam__1(x_66, x_43, x_70, x_2, x_3);
x_32 = x_71;
goto block_40;
}
}
case 3:
{
uint8_t x_97; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_12);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_12, x_3);
lean_dec_ref(x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_99, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_100;
goto block_40;
}
else
{
lean_object* x_101; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec_ref(x_98);
x_20 = x_101;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_12, 0);
lean_inc(x_102);
lean_dec(x_12);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_103, x_3);
lean_dec_ref(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_105, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_106;
goto block_40;
}
else
{
lean_object* x_107; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec_ref(x_104);
x_20 = x_107;
x_21 = lean_box(0);
goto block_31;
}
}
}
case 4:
{
lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_12);
lean_dec_ref(x_43);
lean_dec(x_7);
x_108 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__3));
lean_inc(x_3);
lean_inc_ref(x_2);
x_109 = l_Lean_Environment_Replay_x27_replayConstant(x_108, x_2, x_3);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec_ref(x_109);
x_110 = lean_box(4);
x_111 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_110, x_3);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_112, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_113;
goto block_40;
}
else
{
lean_object* x_114; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec_ref(x_111);
x_20 = x_114;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_115; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec_ref(x_109);
x_20 = x_115;
x_21 = lean_box(0);
goto block_31;
}
}
case 5:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_116 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_116);
lean_dec_ref(x_12);
x_117 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 3);
lean_inc(x_119);
lean_dec_ref(x_116);
x_120 = lean_box(0);
x_121 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_119, x_120, x_2);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_box(0);
x_124 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_122, x_123, x_3);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
lean_dec_ref(x_124);
x_125 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(x_122, x_120, x_2, x_3);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_126);
x_127 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_126, x_123, x_2, x_3);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_127);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_dec_ref(x_117);
x_129 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(x_126, x_120);
x_130 = 0;
x_131 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_118);
lean_ctor_set(x_131, 2, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*3, x_130);
x_132 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_131, x_3);
lean_dec_ref(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_133, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_134;
goto block_40;
}
else
{
lean_object* x_135; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec_ref(x_132);
x_20 = x_135;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_136; 
lean_dec(x_126);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_3);
lean_dec_ref(x_2);
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
lean_dec_ref(x_127);
x_20 = x_136;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_137; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_3);
lean_dec_ref(x_2);
x_137 = lean_ctor_get(x_125, 0);
lean_inc(x_137);
lean_dec_ref(x_125);
x_20 = x_137;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_138; 
lean_dec(x_122);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_124, 0);
lean_inc(x_138);
lean_dec_ref(x_124);
x_20 = x_138;
x_21 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_139; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_3);
lean_dec_ref(x_2);
x_139 = lean_ctor_get(x_121, 0);
lean_inc(x_139);
lean_dec_ref(x_121);
x_20 = x_139;
x_21 = lean_box(0);
goto block_31;
}
}
case 6:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_140 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_140);
lean_dec_ref(x_12);
x_141 = lean_st_ref_take(x_3);
x_142 = lean_ctor_get(x_140, 0);
lean_inc_ref(x_142);
lean_dec_ref(x_140);
x_143 = !lean_is_exclusive(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_141, 3);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec_ref(x_142);
x_146 = l_Lean_NameSet_insert(x_144, x_145);
lean_ctor_set(x_141, 3, x_146);
x_147 = lean_st_ref_set(x_3, x_141);
x_148 = lean_box(0);
x_149 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_148, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_149;
goto block_40;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_141, 0);
x_151 = lean_ctor_get(x_141, 1);
x_152 = lean_ctor_get(x_141, 2);
x_153 = lean_ctor_get(x_141, 3);
x_154 = lean_ctor_get(x_141, 4);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_141);
x_155 = lean_ctor_get(x_142, 0);
lean_inc(x_155);
lean_dec_ref(x_142);
x_156 = l_Lean_NameSet_insert(x_153, x_155);
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_150);
lean_ctor_set(x_157, 1, x_151);
lean_ctor_set(x_157, 2, x_152);
lean_ctor_set(x_157, 3, x_156);
lean_ctor_set(x_157, 4, x_154);
x_158 = lean_st_ref_set(x_3, x_157);
x_159 = lean_box(0);
x_160 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_159, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_160;
goto block_40;
}
}
default: 
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec_ref(x_43);
lean_dec(x_7);
x_161 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_12);
x_162 = lean_st_ref_take(x_3);
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
lean_dec_ref(x_161);
x_164 = !lean_is_exclusive(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_162, 4);
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
lean_dec_ref(x_163);
x_167 = l_Lean_NameSet_insert(x_165, x_166);
lean_ctor_set(x_162, 4, x_167);
x_168 = lean_st_ref_set(x_3, x_162);
x_169 = lean_box(0);
x_170 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_169, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_170;
goto block_40;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_162, 0);
x_172 = lean_ctor_get(x_162, 1);
x_173 = lean_ctor_get(x_162, 2);
x_174 = lean_ctor_get(x_162, 3);
x_175 = lean_ctor_get(x_162, 4);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_162);
x_176 = lean_ctor_get(x_163, 0);
lean_inc(x_176);
lean_dec_ref(x_163);
x_177 = l_Lean_NameSet_insert(x_175, x_176);
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set(x_178, 4, x_177);
x_179 = lean_st_ref_set(x_3, x_178);
x_180 = lean_box(0);
x_181 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_180, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_32 = x_181;
goto block_40;
}
}
}
}
block_31:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__0));
x_23 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_19);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__1));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_io_error_to_string(x_20);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(18, 1, 0);
} else {
 x_29 = x_13;
 lean_ctor_set_tag(x_29, 18);
}
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_16)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_16;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
block_40:
{
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec_ref(x_32);
x_20 = x_39;
x_21 = lean_box(0);
goto block_31;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_182 = lean_obj_once(&l_Lean_Environment_Replay_x27_replayConstant___closed__7, &l_Lean_Environment_Replay_x27_replayConstant___closed__7_once, _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7);
x_183 = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(x_182, x_2, x_3);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_5);
if (x_184 == 0)
{
return x_5;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_5, 0);
lean_inc(x_185);
lean_dec(x_5);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
return x_186;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_Environment_Replay_x27_replayConstant(x_6, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_11;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_5, x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_replayConstants(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_x27_replayConstant(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_2, x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_st_ref_get(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
lean_inc(x_6);
x_22 = lean_environment_find(x_21, x_6);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 6)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 6)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_instBEqConstructorVal_beq(x_24, x_28);
lean_dec_ref(x_28);
lean_dec_ref(x_24);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_30 = 1;
x_31 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_30);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
lean_ctor_set_tag(x_26, 18);
lean_ctor_set(x_26, 0, x_33);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_34; 
lean_free_object(x_26);
lean_free_object(x_17);
lean_dec(x_6);
x_34 = lean_box(0);
x_1 = x_34;
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = l_Lean_instBEqConstructorVal_beq(x_24, x_36);
lean_dec_ref(x_36);
lean_dec_ref(x_24);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_38 = 1;
x_39 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
x_40 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_38);
x_41 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; 
lean_free_object(x_17);
lean_dec(x_6);
x_43 = lean_box(0);
x_1 = x_43;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_24);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
x_45 = lean_st_ref_get(x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec(x_45);
lean_inc(x_6);
x_47 = lean_environment_find(x_46, x_6);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
if (lean_obj_tag(x_48) == 6)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec_ref(x_48);
x_50 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 6)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = l_Lean_instBEqConstructorVal_beq(x_49, x_52);
lean_dec_ref(x_52);
lean_dec_ref(x_49);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_8);
x_55 = 1;
x_56 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
x_57 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_55);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(18, 1, 0);
} else {
 x_59 = x_53;
 lean_ctor_set_tag(x_59, 18);
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_6);
x_61 = lean_box(0);
x_1 = x_61;
x_2 = x_8;
goto _start;
}
}
else
{
lean_dec(x_51);
lean_dec_ref(x_49);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_48);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_47);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_17;
}
block_16:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0));
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_6, x_5, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_checkPostponedConstructors(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_st_ref_get(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
lean_inc(x_6);
x_22 = lean_environment_find(x_21, x_6);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 7)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 7)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_instBEqRecursorVal_beq(x_24, x_28);
lean_dec_ref(x_28);
lean_dec_ref(x_24);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_30 = 1;
x_31 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_30);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
lean_ctor_set_tag(x_26, 18);
lean_ctor_set(x_26, 0, x_33);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_34; 
lean_free_object(x_26);
lean_free_object(x_17);
lean_dec(x_6);
x_34 = lean_box(0);
x_1 = x_34;
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = l_Lean_instBEqRecursorVal_beq(x_24, x_36);
lean_dec_ref(x_36);
lean_dec_ref(x_24);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_38 = 1;
x_39 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
x_40 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_38);
x_41 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
else
{
lean_object* x_43; 
lean_free_object(x_17);
lean_dec(x_6);
x_43 = lean_box(0);
x_1 = x_43;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_26);
lean_dec_ref(x_24);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_23);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_22);
lean_free_object(x_17);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_17);
x_45 = lean_st_ref_get(x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
lean_dec(x_45);
lean_inc(x_6);
x_47 = lean_environment_find(x_46, x_6);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
if (lean_obj_tag(x_48) == 7)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec_ref(x_48);
x_50 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
if (lean_obj_tag(x_51) == 7)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = l_Lean_instBEqRecursorVal_beq(x_49, x_52);
lean_dec_ref(x_52);
lean_dec_ref(x_49);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_8);
x_55 = 1;
x_56 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
x_57 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_55);
x_58 = lean_string_append(x_56, x_57);
lean_dec_ref(x_57);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(18, 1, 0);
} else {
 x_59 = x_53;
 lean_ctor_set_tag(x_59, 18);
}
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_6);
x_61 = lean_box(0);
x_1 = x_61;
x_2 = x_8;
goto _start;
}
}
else
{
lean_dec(x_51);
lean_dec_ref(x_49);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_48);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_47);
lean_dec(x_8);
x_9 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_17;
}
block_16:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0));
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_6, x_5, x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_x27_checkPostponedRecursors(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget_borrowed(x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(x_4, x_8);
lean_dec(x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_isUnsafe(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_ConstantInfo_isPartial(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_NameSet_insert(x_2, x_7);
x_1 = x_6;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_box(1);
x_35 = lean_box(0);
x_36 = lean_array_get_size(x_19);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
x_21 = x_35;
goto block_34;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_36);
x_40 = 0;
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(x_19, x_39, x_40, x_35);
x_21 = x_41;
goto block_34;
}
block_18:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_elab_environment_of_kernel_env(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_11 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_elab_environment_of_kernel_env(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
block_34:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_elab_environment_to_kernel_env(x_2);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_20);
x_26 = lean_st_mk_ref(x_25);
x_27 = lean_box(0);
lean_inc(x_26);
lean_inc_ref(x_1);
x_28 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_27, x_23, x_1, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l_Lean_Environment_Replay_x27_checkPostponedConstructors(x_1, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec_ref(x_29);
x_30 = l_Lean_Environment_Replay_x27_checkPostponedRecursors(x_1, x_26);
lean_dec_ref(x_1);
x_4 = x_26;
x_5 = x_30;
goto block_18;
}
else
{
lean_dec_ref(x_1);
x_4 = x_26;
x_5 = x_29;
goto block_18;
}
}
else
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_replay_x27(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanChecker_Replay(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
