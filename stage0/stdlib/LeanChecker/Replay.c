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
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_9 = lean_st_ref_take(x_2);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 4);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_15 = x_9;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_11);
x_18 = l_Lean_NameSet_insert(x_12, x_1);
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_18);
lean_ctor_set(x_15, 1, x_17);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_set(x_2, x_19);
x_21 = lean_box(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_33; 
x_11 = lean_ctor_get(x_8, 0);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
x_12 = x_8;
x_13 = x_33;
goto block_32;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
x_14 = lean_st_ref_take(x_2);
x_15 = lean_ctor_get(x_14, 1);
x_16 = lean_ctor_get(x_14, 2);
x_17 = lean_ctor_get(x_14, 3);
x_18 = lean_ctor_get(x_14, 4);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_19 = x_14;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_21; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_11);
x_21 = x_19;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_16);
lean_ctor_set(x_28, 3, x_17);
lean_ctor_set(x_28, 4, x_18);
x_21 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_st_ref_set(x_2, x_21);
x_23 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_6 = lean_st_ref_take(x_4);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_ctor_get(x_6, 3);
x_11 = lean_ctor_get(x_6, 4);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_12 = x_6;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_1, x_9);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_14);
x_15 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_10);
lean_ctor_set(x_20, 4, x_11);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_set(x_4, x_15);
x_17 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_8, 0);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
x_12 = x_8;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_6 = x_1;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_ConstantInfo_name(x_4);
x_9 = l_Lean_ConstantInfo_type(x_4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_10);
x_11 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_2);
x_11 = x_14;
goto block_13;
}
block_13:
{
x_1 = x_5;
x_2 = x_11;
goto _start;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_6 = x_1;
x_7 = x_20;
goto block_19;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_ConstantInfo_name(x_8);
x_11 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(x_9, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_14);
x_15 = x_6;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_2);
x_15 = x_18;
goto block_17;
}
block_17:
{
x_1 = x_5;
x_2 = x_15;
goto _start;
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_st_ref_take(x_3);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_ctor_get(x_8, 3);
x_13 = lean_ctor_get(x_8, 4);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
x_14 = x_8;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_ConstantInfo_name(x_6);
x_17 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_16, x_10);
x_18 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(x_16, x_11);
lean_dec(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_18);
lean_ctor_set(x_14, 1, x_17);
x_19 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_12);
lean_ctor_set(x_24, 4, x_13);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_1 = x_7;
x_2 = x_21;
goto _start;
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_9 = x_1;
x_10 = x_18;
goto block_17;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_instInhabitedConstantInfo_default;
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(x_11, x_3, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_2);
x_13 = x_16;
goto block_15;
}
block_15:
{
x_1 = x_8;
x_2 = x_13;
goto _start;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_23; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
x_10 = x_1;
x_11 = x_23;
goto block_22;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_ConstantInfo_inductiveVal_x21(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_13, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_2);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_1 = x_9;
x_2 = x_18;
goto _start;
}
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_206; 
x_6 = lean_ctor_get(x_5, 0);
x_206 = !lean_is_exclusive(x_5);
if (x_206 == 0)
{
x_7 = x_5;
x_8 = x_206;
goto block_205;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_206;
goto block_205;
}
block_205:
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_2, x_1);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_202; 
x_15 = lean_ctor_get(x_14, 0);
x_202 = !lean_is_exclusive(x_14);
if (x_202 == 0)
{
x_16 = x_14;
x_17 = x_202;
goto block_201;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_15);
x_18 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_15);
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = l_Lean_Environment_Replay_x27_replayConstants(x_18, x_2, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_199; 
x_199 = !lean_is_exclusive(x_19);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_19, 0);
lean_dec(x_200);
x_20 = x_19;
x_21 = x_199;
goto block_198;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_40; 
x_22 = lean_st_ref_get(x_3);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_52);
x_53 = x_7;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
else
{
lean_object* x_56; 
lean_inc(x_1);
x_56 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(x_56, 0, x_1);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_68; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_57 = lean_ctor_get(x_15, 0);
x_68 = !lean_is_exclusive(x_15);
if (x_68 == 0)
{
x_58 = x_15;
x_59 = x_68;
goto block_67;
}
else
{
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_box(0);
x_59 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_57);
x_60 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_61; 
x_61 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_60, x_3);
lean_dec_ref(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_62, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_63;
goto block_51;
}
else
{
lean_object* x_64; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec_ref(x_61);
x_25 = x_64;
goto block_39;
}
}
}
}
case 1:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_80; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_69 = lean_ctor_get(x_15, 0);
x_80 = !lean_is_exclusive(x_15);
if (x_80 == 0)
{
x_70 = x_15;
x_71 = x_80;
goto block_79;
}
else
{
lean_inc(x_69);
lean_dec(x_15);
x_70 = lean_box(0);
x_71 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_69);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; 
x_73 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_72, x_3);
lean_dec_ref(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_74, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_75;
goto block_51;
}
else
{
lean_object* x_76; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec_ref(x_73);
x_25 = x_76;
goto block_39;
}
}
}
}
case 2:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_81);
x_82 = lean_st_ref_get(x_3);
x_83 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_83);
lean_dec(x_82);
lean_inc_ref(x_56);
lean_inc_ref(x_81);
x_84 = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(x_84, 0, x_81);
lean_closure_set(x_84, 1, x_56);
x_88 = l_Lean_ConstantInfo_name(x_15);
lean_dec_ref(x_15);
x_89 = lean_environment_find(x_83, x_88);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 2)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_110; 
lean_dec_ref(x_89);
lean_dec_ref(x_84);
x_91 = lean_ctor_get(x_81, 0);
x_92 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_92);
lean_dec_ref(x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_81, 2);
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
x_97 = lean_ctor_get(x_91, 2);
x_98 = lean_ctor_get(x_92, 2);
lean_inc(x_98);
lean_dec_ref(x_92);
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 2);
lean_inc_ref(x_101);
lean_dec_ref(x_93);
x_110 = lean_name_eq(x_95, x_99);
lean_dec(x_99);
if (x_110 == 0)
{
lean_dec_ref(x_101);
x_102 = x_110;
goto block_109;
}
else
{
uint8_t x_111; 
x_111 = lean_expr_eqv(x_97, x_101);
lean_dec_ref(x_101);
x_102 = x_111;
goto block_109;
}
block_109:
{
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_98);
lean_del_object(x_7);
goto block_87;
}
else
{
uint8_t x_103; 
x_103 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_96, x_100);
lean_dec(x_100);
if (x_103 == 0)
{
lean_dec(x_98);
lean_del_object(x_7);
goto block_87;
}
else
{
uint8_t x_104; 
x_104 = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(x_94, x_98);
lean_dec(x_98);
if (x_104 == 0)
{
lean_del_object(x_7);
goto block_87;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_81);
lean_dec_ref(x_56);
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_105 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_105);
x_106 = x_7;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_90);
lean_dec_ref(x_81);
lean_dec_ref(x_56);
lean_del_object(x_7);
x_112 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_84, x_89, x_2, x_3);
lean_dec_ref(x_89);
x_40 = x_112;
goto block_51;
}
}
else
{
lean_object* x_113; 
lean_dec_ref(x_81);
lean_dec_ref(x_56);
lean_del_object(x_7);
x_113 = l_Lean_Environment_Replay_x27_replayConstant___lam__2(x_84, x_89, x_2, x_3);
lean_dec(x_89);
x_40 = x_113;
goto block_51;
}
block_87:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box(0);
x_86 = l_Lean_Environment_Replay_x27_replayConstant___lam__1(x_81, x_56, x_85, x_2, x_3);
x_40 = x_86;
goto block_51;
}
}
case 3:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_125; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_114 = lean_ctor_get(x_15, 0);
x_125 = !lean_is_exclusive(x_15);
if (x_125 == 0)
{
x_115 = x_15;
x_116 = x_125;
goto block_124;
}
else
{
lean_inc(x_114);
lean_dec(x_15);
x_115 = lean_box(0);
x_116 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_114);
x_117 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_118; 
x_118 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_117, x_3);
lean_dec_ref(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_119, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_120;
goto block_51;
}
else
{
lean_object* x_121; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec_ref(x_118);
x_25 = x_121;
goto block_39;
}
}
}
}
case 4:
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_15);
lean_dec_ref(x_56);
lean_del_object(x_7);
x_126 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__3));
lean_inc(x_3);
lean_inc_ref(x_2);
x_127 = l_Lean_Environment_Replay_x27_replayConstant(x_126, x_2, x_3);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_127);
x_128 = lean_box(4);
x_129 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_128, x_3);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_130, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_131;
goto block_51;
}
else
{
lean_object* x_132; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec_ref(x_129);
x_25 = x_132;
goto block_39;
}
}
else
{
lean_object* x_133; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
lean_dec_ref(x_127);
x_25 = x_133;
goto block_39;
}
}
case 5:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_134 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_134);
lean_dec_ref(x_15);
x_135 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 3);
lean_inc(x_137);
lean_dec_ref(x_134);
x_138 = lean_box(0);
x_139 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(x_137, x_138, x_2);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_box(0);
x_142 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(x_140, x_141, x_3);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec_ref(x_142);
x_143 = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(x_140, x_138, x_2, x_3);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_144);
x_145 = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(x_144, x_141, x_2, x_3);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
lean_dec_ref(x_145);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_dec_ref(x_135);
x_147 = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(x_144, x_138);
x_148 = 0;
x_149 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set(x_149, 2, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*3, x_148);
x_150 = l_Lean_Environment_Replay_x27_addDecl___redArg(x_149, x_3);
lean_dec_ref(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_151, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_152;
goto block_51;
}
else
{
lean_object* x_153; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec_ref(x_150);
x_25 = x_153;
goto block_39;
}
}
else
{
lean_object* x_154; 
lean_dec(x_144);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_3);
lean_dec_ref(x_2);
x_154 = lean_ctor_get(x_145, 0);
lean_inc(x_154);
lean_dec_ref(x_145);
x_25 = x_154;
goto block_39;
}
}
else
{
lean_object* x_155; 
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_3);
lean_dec_ref(x_2);
x_155 = lean_ctor_get(x_143, 0);
lean_inc(x_155);
lean_dec_ref(x_143);
x_25 = x_155;
goto block_39;
}
}
else
{
lean_object* x_156; 
lean_dec(x_140);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_3);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_142, 0);
lean_inc(x_156);
lean_dec_ref(x_142);
x_25 = x_156;
goto block_39;
}
}
else
{
lean_object* x_157; 
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_3);
lean_dec_ref(x_2);
x_157 = lean_ctor_get(x_139, 0);
lean_inc(x_157);
lean_dec_ref(x_139);
x_25 = x_157;
goto block_39;
}
}
case 6:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_177; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_158 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_158);
lean_dec_ref(x_15);
x_159 = lean_st_ref_take(x_3);
x_160 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_160);
lean_dec_ref(x_158);
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_ctor_get(x_159, 1);
x_163 = lean_ctor_get(x_159, 2);
x_164 = lean_ctor_get(x_159, 3);
x_165 = lean_ctor_get(x_159, 4);
x_177 = !lean_is_exclusive(x_159);
if (x_177 == 0)
{
x_166 = x_159;
x_167 = x_177;
goto block_176;
}
else
{
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_159);
x_166 = lean_box(0);
x_167 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
lean_dec_ref(x_160);
x_169 = l_Lean_NameSet_insert(x_164, x_168);
if (x_167 == 0)
{
lean_ctor_set(x_166, 3, x_169);
x_170 = x_166;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_162);
lean_ctor_set(x_175, 2, x_163);
lean_ctor_set(x_175, 3, x_169);
lean_ctor_set(x_175, 4, x_165);
x_170 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_st_ref_set(x_3, x_170);
x_172 = lean_box(0);
x_173 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_172, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_173;
goto block_51;
}
}
}
default: 
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_197; 
lean_dec_ref(x_56);
lean_del_object(x_7);
x_178 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_178);
lean_dec_ref(x_15);
x_179 = lean_st_ref_take(x_3);
x_180 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_180);
lean_dec_ref(x_178);
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = lean_ctor_get(x_179, 2);
x_184 = lean_ctor_get(x_179, 3);
x_185 = lean_ctor_get(x_179, 4);
x_197 = !lean_is_exclusive(x_179);
if (x_197 == 0)
{
x_186 = x_179;
x_187 = x_197;
goto block_196;
}
else
{
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_179);
x_186 = lean_box(0);
x_187 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_180, 0);
lean_inc(x_188);
lean_dec_ref(x_180);
x_189 = l_Lean_NameSet_insert(x_185, x_188);
if (x_187 == 0)
{
lean_ctor_set(x_186, 4, x_189);
x_190 = x_186;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_195, 0, x_181);
lean_ctor_set(x_195, 1, x_182);
lean_ctor_set(x_195, 2, x_183);
lean_ctor_set(x_195, 3, x_184);
lean_ctor_set(x_195, 4, x_189);
x_190 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_st_ref_set(x_3, x_190);
x_192 = lean_box(0);
x_193 = l_Lean_Environment_Replay_x27_replayConstant___lam__0(x_1, x_192, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_40 = x_193;
goto block_51;
}
}
}
}
}
block_39:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__0));
x_27 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_24);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__1));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_io_error_to_string(x_25);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 18);
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_33);
x_34 = x_20;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
block_51:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_49; 
lean_del_object(x_20);
lean_del_object(x_16);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
x_42 = x_40;
x_43 = x_49;
goto block_48;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_44);
x_45 = x_42;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec_ref(x_40);
x_25 = x_50;
goto block_39;
}
}
}
}
else
{
lean_del_object(x_16);
lean_dec(x_15);
lean_del_object(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_14);
lean_del_object(x_7);
lean_dec(x_1);
x_203 = lean_obj_once(&l_Lean_Environment_Replay_x27_replayConstant___closed__7, &l_Lean_Environment_Replay_x27_replayConstant___closed__7_once, _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7);
x_204 = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(x_203, x_2, x_3);
return x_204;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_5, 0);
x_214 = !lean_is_exclusive(x_5);
if (x_214 == 0)
{
x_208 = x_5;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_dec(x_5);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_14 = x_10;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
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
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
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
lean_object* x_7; uint8_t x_8; uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_7 = x_6;
x_8 = x_13;
goto block_12;
}
else
{
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_5);
x_9 = x_7;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_16 = x_6;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_16 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_16, 0);
lean_dec(x_46);
x_17 = x_16;
x_18 = x_45;
goto block_44;
}
else
{
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_st_ref_get(x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
lean_inc(x_6);
x_21 = lean_environment_find(x_20, x_6);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_22) == 6)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 6)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_43; 
x_26 = lean_ctor_get(x_25, 0);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
x_27 = x_25;
x_28 = x_43;
goto block_42;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqConstructorVal_beq(x_23, x_26);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_30 = 1;
x_31 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_30);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 18);
lean_ctor_set(x_27, 0, x_33);
x_34 = x_27;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_34);
x_35 = x_17;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_40; 
lean_del_object(x_27);
lean_del_object(x_17);
lean_dec(x_6);
x_40 = lean_box(0);
x_1 = x_40;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_23);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_22);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_21);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_16;
}
block_15:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0));
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
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
lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_8 = x_7;
x_9 = x_14;
goto block_13;
}
else
{
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_6);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_17 = x_7;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
x_16 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_16, 0);
lean_dec(x_46);
x_17 = x_16;
x_18 = x_45;
goto block_44;
}
else
{
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_st_ref_get(x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
lean_inc(x_6);
x_21 = lean_environment_find(x_20, x_6);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(x_3, x_6);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_43; 
x_26 = lean_ctor_get(x_25, 0);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
x_27 = x_25;
x_28 = x_43;
goto block_42;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqRecursorVal_beq(x_23, x_26);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_30 = 1;
x_31 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
x_32 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_30);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 18);
lean_ctor_set(x_27, 0, x_33);
x_34 = x_27;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_33);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_34);
x_35 = x_17;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_40; 
lean_del_object(x_27);
lean_del_object(x_17);
lean_dec(x_6);
x_40 = lean_box(0);
x_1 = x_40;
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_25);
lean_dec_ref(x_23);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_22);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
else
{
lean_dec(x_21);
lean_del_object(x_17);
lean_dec(x_8);
goto block_15;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
return x_16;
}
block_15:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0));
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
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
lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_8 = x_7;
x_9 = x_14;
goto block_13;
}
else
{
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_6);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_17 = x_7;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_box(1);
x_47 = lean_box(0);
x_48 = lean_array_get_size(x_26);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
if (x_50 == 0)
{
x_28 = x_47;
goto block_46;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = lean_usize_of_nat(x_48);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(x_26, x_51, x_52, x_47);
x_28 = x_53;
goto block_46;
}
block_25:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_6 = x_5;
x_7 = x_15;
goto block_14;
}
else
{
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_elab_environment_of_kernel_env(x_9);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_10);
x_11 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_5, 0);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
x_18 = x_5;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
block_46:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_elab_environment_to_kernel_env(x_2);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_27);
x_33 = lean_st_mk_ref(x_32);
x_34 = lean_box(0);
lean_inc(x_33);
lean_inc_ref(x_1);
x_35 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(x_34, x_30, x_1, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Lean_Environment_Replay_x27_checkPostponedConstructors(x_1, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
x_37 = l_Lean_Environment_Replay_x27_checkPostponedRecursors(x_1, x_33);
lean_dec_ref(x_1);
x_4 = x_33;
x_5 = x_37;
goto block_25;
}
else
{
lean_dec_ref(x_1);
x_4 = x_33;
x_5 = x_36;
goto block_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_33);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_35, 0);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
x_39 = x_35;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
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
res = initialize_Lean_CoreM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
