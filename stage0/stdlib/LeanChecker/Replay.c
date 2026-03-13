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
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__0 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__0_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':\n"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__1 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__1_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__2 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value;
static const lean_ctor_object l_Lean_Environment_Replay_x27_replayConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__3 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__6 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__6_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Environment.Replay'.replayConstant"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__5 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__5_value;
static const lean_string_object l_Lean_Environment_Replay_x27_replayConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LeanChecker.Replay"};
static const lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__4 = (const lean_object*)&l_Lean_Environment_Replay_x27_replayConstant___closed__4_value;
static lean_once_cell_t l_Lean_Environment_Replay_x27_replayConstant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Environment_Replay_x27_replayConstant___closed__7;
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "No such recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg(lean_object* v_name_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_remaining_5_; uint8_t v___x_6_; 
v___x_4_ = lean_st_ref_get(v_a_2_);
v_remaining_5_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_remaining_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1_, v_remaining_5_);
lean_dec(v_remaining_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec(v_name_1_);
v___x_7_ = lean_box(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v_env_10_; lean_object* v_remaining_11_; lean_object* v_pending_12_; lean_object* v_postponedConstructors_13_; lean_object* v_postponedRecursors_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_26_; 
v___x_9_ = lean_st_ref_take(v_a_2_);
v_env_10_ = lean_ctor_get(v___x_9_, 0);
v_remaining_11_ = lean_ctor_get(v___x_9_, 1);
v_pending_12_ = lean_ctor_get(v___x_9_, 2);
v_postponedConstructors_13_ = lean_ctor_get(v___x_9_, 3);
v_postponedRecursors_14_ = lean_ctor_get(v___x_9_, 4);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_26_ == 0)
{
v___x_16_ = v___x_9_;
v_isShared_17_ = v_isSharedCheck_26_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_postponedRecursors_14_);
lean_inc(v_postponedConstructors_13_);
lean_inc(v_pending_12_);
lean_inc(v_remaining_11_);
lean_inc(v_env_10_);
lean_dec(v___x_9_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_26_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_18_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_name_1_, v_remaining_11_);
v___x_19_ = l_Lean_NameSet_insert(v_pending_12_, v_name_1_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 2, v___x_19_);
lean_ctor_set(v___x_16_, 1, v___x_18_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_env_10_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v___x_19_);
lean_ctor_set(v_reuseFailAlloc_25_, 3, v_postponedConstructors_13_);
lean_ctor_set(v_reuseFailAlloc_25_, 4, v_postponedRecursors_14_);
v___x_21_ = v_reuseFailAlloc_25_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_st_ref_set(v_a_2_, v___x_21_);
v___x_23_ = lean_box(v___x_6_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___redArg___boxed(lean_object* v_name_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Environment_Replay_x27_isTodo___redArg(v_name_27_, v_a_28_);
lean_dec(v_a_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo(lean_object* v_name_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Environment_Replay_x27_isTodo___redArg(v_name_31_, v_a_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_isTodo___boxed(lean_object* v_name_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Environment_Replay_x27_isTodo(v_name_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg(lean_object* v_ex_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_43_ = l_Lean_Options_empty;
v___x_44_ = l_Lean_Kernel_Exception_toMessageData(v_ex_41_, v___x_43_);
v___x_45_ = l_Lean_MessageData_toString(v___x_44_);
v___x_46_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___redArg___boxed(lean_object* v_ex_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Environment_Replay_x27_throwKernelException___redArg(v_ex_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException(lean_object* v_ex_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Environment_Replay_x27_throwKernelException___redArg(v_ex_51_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_throwKernelException___boxed(lean_object* v_ex_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Environment_Replay_x27_throwKernelException(v_ex_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg(lean_object* v_d_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_env_65_; size_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_64_ = lean_st_ref_get(v_a_62_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = ((size_t)0ULL);
v___x_67_ = lean_box(0);
v___x_68_ = lean_add_decl(v_env_65_, v___x_66_, v_d_61_, v___x_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = l_Lean_Environment_Replay_x27_throwKernelException___redArg(v_a_69_);
return v___x_70_;
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_93_; 
v_a_71_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_93_ == 0)
{
v___x_73_ = v___x_68_;
v_isShared_74_ = v_isSharedCheck_93_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_68_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_93_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v_remaining_76_; lean_object* v_pending_77_; lean_object* v_postponedConstructors_78_; lean_object* v_postponedRecursors_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_91_; 
v___x_75_ = lean_st_ref_take(v_a_62_);
v_remaining_76_ = lean_ctor_get(v___x_75_, 1);
v_pending_77_ = lean_ctor_get(v___x_75_, 2);
v_postponedConstructors_78_ = lean_ctor_get(v___x_75_, 3);
v_postponedRecursors_79_ = lean_ctor_get(v___x_75_, 4);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_75_, 0);
lean_dec(v_unused_92_);
v___x_81_ = v___x_75_;
v_isShared_82_ = v_isSharedCheck_91_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_postponedRecursors_79_);
lean_inc(v_postponedConstructors_78_);
lean_inc(v_pending_77_);
lean_inc(v_remaining_76_);
lean_dec(v___x_75_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_91_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v_a_71_);
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_remaining_76_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v_pending_77_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_postponedConstructors_78_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v_postponedRecursors_79_);
v___x_84_ = v_reuseFailAlloc_90_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = lean_st_ref_set(v_a_62_, v___x_84_);
v___x_86_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set_tag(v___x_73_, 0);
lean_ctor_set(v___x_73_, 0, v___x_86_);
v___x_88_ = v___x_73_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___redArg___boxed(lean_object* v_d_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v_d_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec(v_d_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl(lean_object* v_d_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v_d_98_, v_a_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_addDecl___boxed(lean_object* v_d_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Environment_Replay_x27_addDecl(v_d_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_d_103_);
return v_res_107_;
}
}
static lean_object* _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___f_117_; lean_object* v___x_37084__overap_118_; lean_object* v___x_119_; 
v___x_113_ = lean_obj_once(&l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0, &l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0_once, _init_l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___closed__0);
v___x_114_ = l_ReaderT_instMonad___redArg(v___x_113_);
v___x_115_ = lean_box(0);
v___x_116_ = l_instInhabitedOfMonad___redArg(v___x_114_, v___x_115_);
v___f_117_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_117_, 0, v___x_116_);
v___x_37084__overap_118_ = lean_panic_fn(v___f_117_, v_msg_109_);
v___x_119_ = lean_apply_3(v___x_37084__overap_118_, v___y_110_, v___y_111_, lean_box(0));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7___boxed(lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(v_msg_120_, v___y_121_, v___y_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0(lean_object* v_name_127_, lean_object* v_____r_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; lean_object* v_env_133_; lean_object* v_remaining_134_; lean_object* v_pending_135_; lean_object* v_postponedConstructors_136_; lean_object* v_postponedRecursors_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_148_; 
v___x_132_ = lean_st_ref_take(v___y_130_);
v_env_133_ = lean_ctor_get(v___x_132_, 0);
v_remaining_134_ = lean_ctor_get(v___x_132_, 1);
v_pending_135_ = lean_ctor_get(v___x_132_, 2);
v_postponedConstructors_136_ = lean_ctor_get(v___x_132_, 3);
v_postponedRecursors_137_ = lean_ctor_get(v___x_132_, 4);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_148_ == 0)
{
v___x_139_ = v___x_132_;
v_isShared_140_ = v_isSharedCheck_148_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_postponedRecursors_137_);
lean_inc(v_postponedConstructors_136_);
lean_inc(v_pending_135_);
lean_inc(v_remaining_134_);
lean_inc(v_env_133_);
lean_dec(v___x_132_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_148_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_name_127_, v_pending_135_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 2, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_env_133_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_remaining_134_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_postponedConstructors_136_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_postponedRecursors_137_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_st_ref_set(v___y_130_, v___x_143_);
v___x_145_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___closed__0));
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed(lean_object* v_name_149_, lean_object* v_____r_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_149_, v_____r_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v_name_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1(lean_object* v_val_155_, lean_object* v___f_156_, lean_object* v_____r_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_161_, 0, v_val_155_);
v___x_162_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_161_, v___y_159_);
lean_dec_ref(v___x_161_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref(v___x_162_);
v___x_164_ = lean_apply_4(v___f_156_, v_a_163_, v___y_158_, v___y_159_, lean_box(0));
return v___x_164_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec_ref(v___f_156_);
v_a_165_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_162_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_162_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed(lean_object* v_val_173_, lean_object* v___f_174_, lean_object* v_____r_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Environment_Replay_x27_replayConstant___lam__1(v_val_173_, v___f_174_, v_____r_175_, v___y_176_, v___y_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2(lean_object* v___f_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_4(v___f_180_, v___x_185_, v___y_182_, v___y_183_, lean_box(0));
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___lam__2___boxed(lean_object* v___f_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Environment_Replay_x27_replayConstant___lam__2(v___f_187_, v_x_188_, v___y_189_, v___y_190_);
lean_dec(v_x_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
if (lean_obj_tag(v_a_193_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = l_List_reverse___redArg(v_a_194_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_head_196_ = lean_ctor_get(v_a_193_, 0);
v_tail_197_ = lean_ctor_get(v_a_193_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_a_193_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v_a_193_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_tail_197_);
lean_inc(v_head_196_);
lean_dec(v_a_193_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_201_ = l_Lean_ConstantInfo_name(v_head_196_);
v___x_202_ = l_Lean_ConstantInfo_type(v_head_196_);
lean_dec(v_head_196_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v_a_194_);
lean_ctor_set(v___x_199_, 0, v___x_203_);
v___x_205_ = v___x_199_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_a_194_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v_a_193_ = v_tail_197_;
v_a_194_ = v___x_205_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
if (lean_obj_tag(v_a_209_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = l_List_reverse___redArg(v_a_210_);
return v___x_211_;
}
else
{
lean_object* v_head_212_; lean_object* v_tail_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_228_; 
v_head_212_ = lean_ctor_get(v_a_209_, 0);
v_tail_213_ = lean_ctor_get(v_a_209_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_228_ == 0)
{
v___x_215_ = v_a_209_;
v_isShared_216_ = v_isSharedCheck_228_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_tail_213_);
lean_inc(v_head_212_);
lean_dec(v_a_209_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_228_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v_fst_217_ = lean_ctor_get(v_head_212_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v_head_212_, 1);
lean_inc(v_snd_218_);
lean_dec(v_head_212_);
v___x_219_ = l_Lean_ConstantInfo_name(v_fst_217_);
v___x_220_ = l_Lean_ConstantInfo_type(v_fst_217_);
lean_dec(v_fst_217_);
v___x_221_ = lean_box(0);
v___x_222_ = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__0(v_snd_218_, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_219_);
lean_ctor_set(v___x_223_, 1, v___x_220_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v_a_210_);
lean_ctor_set(v___x_215_, 0, v___x_223_);
v___x_225_ = v___x_215_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_a_210_);
v___x_225_ = v_reuseFailAlloc_227_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
v_a_209_ = v_tail_213_;
v_a_210_ = v___x_225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(lean_object* v_as_x27_229_, lean_object* v_b_230_, lean_object* v___y_231_){
_start:
{
if (lean_obj_tag(v_as_x27_229_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_b_230_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_tail_235_; lean_object* v___x_236_; lean_object* v_env_237_; lean_object* v_remaining_238_; lean_object* v_pending_239_; lean_object* v_postponedConstructors_240_; lean_object* v_postponedRecursors_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_254_; 
v_head_234_ = lean_ctor_get(v_as_x27_229_, 0);
v_tail_235_ = lean_ctor_get(v_as_x27_229_, 1);
v___x_236_ = lean_st_ref_take(v___y_231_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
v_remaining_238_ = lean_ctor_get(v___x_236_, 1);
v_pending_239_ = lean_ctor_get(v___x_236_, 2);
v_postponedConstructors_240_ = lean_ctor_get(v___x_236_, 3);
v_postponedRecursors_241_ = lean_ctor_get(v___x_236_, 4);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_254_ == 0)
{
v___x_243_ = v___x_236_;
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_postponedRecursors_241_);
lean_inc(v_postponedConstructors_240_);
lean_inc(v_pending_239_);
lean_inc(v_remaining_238_);
lean_inc(v_env_237_);
lean_dec(v___x_236_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_245_ = l_Lean_ConstantInfo_name(v_head_234_);
v___x_246_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v___x_245_, v_remaining_238_);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v___x_245_, v_pending_239_);
lean_dec(v___x_245_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 2, v___x_247_);
lean_ctor_set(v___x_243_, 1, v___x_246_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_env_237_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_postponedConstructors_240_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_postponedRecursors_241_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_st_ref_set(v___y_231_, v___x_249_);
v___x_251_ = lean_box(0);
v_as_x27_229_ = v_tail_235_;
v_b_230_ = v___x_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg___boxed(lean_object* v_as_x27_255_, lean_object* v_b_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(v_as_x27_255_, v_b_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec(v_as_x27_255_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v___y_262_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = l_List_reverse___redArg(v_x_261_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v_head_266_; lean_object* v_tail_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_head_266_ = lean_ctor_get(v_x_260_, 0);
v_tail_267_ = lean_ctor_get(v_x_260_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v_x_260_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_tail_267_);
lean_inc(v_head_266_);
lean_dec(v_x_260_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = l_Lean_instInhabitedConstantInfo_default;
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_throwAlreadyImported_spec__0___redArg(v___x_271_, v___y_262_, v_head_266_);
lean_dec(v_head_266_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_x_261_);
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_x_261_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v_x_260_ = v_tail_267_;
v_x_261_ = v___x_274_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(v_x_278_, v_x_279_, v___y_280_);
lean_dec_ref(v___y_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_List_reverse___redArg(v_x_284_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_305_; 
v_head_290_ = lean_ctor_get(v_x_283_, 0);
v_tail_291_ = lean_ctor_get(v_x_283_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_305_ == 0)
{
v___x_293_ = v_x_283_;
v_isShared_294_ = v_isSharedCheck_305_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_tail_291_);
lean_inc(v_head_290_);
lean_dec(v_x_283_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_305_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v_ctors_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_295_ = l_Lean_ConstantInfo_inductiveVal_x21(v_head_290_);
v_ctors_296_ = lean_ctor_get(v___x_295_, 4);
lean_inc(v_ctors_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = lean_box(0);
v___x_298_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(v_ctors_296_, v___x_297_, v___y_285_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_head_290_);
lean_ctor_set(v___x_300_, 1, v_a_299_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_x_284_);
lean_ctor_set(v___x_293_, 0, v___x_300_);
v___x_302_ = v___x_293_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_x_284_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
v_x_283_ = v_tail_291_;
v_x_284_ = v___x_302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4___boxed(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(v_x_306_, v_x_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(lean_object* v_as_x27_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
if (lean_obj_tag(v_as_x27_317_) == 0)
{
lean_object* v___x_322_; 
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_b_318_);
return v___x_322_;
}
else
{
lean_object* v_head_323_; lean_object* v_tail_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_head_323_ = lean_ctor_get(v_as_x27_317_, 0);
lean_inc(v_head_323_);
v_tail_324_ = lean_ctor_get(v_as_x27_317_, 1);
lean_inc(v_tail_324_);
lean_dec_ref(v_as_x27_317_);
v___x_325_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_323_);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
v___x_326_ = l_Lean_Environment_Replay_x27_replayConstants(v___x_325_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v___x_327_; 
lean_dec_ref(v___x_326_);
v___x_327_ = lean_box(0);
v_as_x27_317_ = v_tail_324_;
v_b_318_ = v___x_327_;
goto _start;
}
else
{
lean_dec(v_tail_324_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(lean_object* v_as_x27_329_, lean_object* v_b_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
if (lean_obj_tag(v_as_x27_329_) == 0)
{
lean_object* v___x_334_; 
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_b_330_);
return v___x_334_;
}
else
{
lean_object* v_head_335_; lean_object* v_tail_336_; lean_object* v_snd_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_head_335_ = lean_ctor_get(v_as_x27_329_, 0);
lean_inc(v_head_335_);
v_tail_336_ = lean_ctor_get(v_as_x27_329_, 1);
lean_inc(v_tail_336_);
lean_dec_ref(v_as_x27_329_);
v_snd_337_ = lean_ctor_get(v_head_335_, 1);
lean_inc(v_snd_337_);
lean_dec(v_head_335_);
v___x_338_ = lean_box(0);
lean_inc(v___y_332_);
lean_inc_ref(v___y_331_);
v___x_339_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(v_snd_337_, v___x_338_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_dec_ref(v___x_339_);
v_as_x27_329_ = v_tail_336_;
v_b_330_ = v___x_338_;
goto _start;
}
else
{
lean_dec(v_tail_336_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v___x_339_;
}
}
}
}
static lean_object* _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__6));
v___x_345_ = lean_unsigned_to_nat(50u);
v___x_346_ = lean_unsigned_to_nat(81u);
v___x_347_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__5));
v___x_348_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__4));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant(lean_object* v_name_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
lean_inc(v_name_350_);
v___x_354_ = l_Lean_Environment_Replay_x27_isTodo___redArg(v_name_350_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_555_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_555_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_555_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_555_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
uint8_t v___x_359_; 
v___x_359_ = lean_unbox(v_a_355_);
lean_dec(v_a_355_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_name_350_);
v___x_360_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_a_351_, v_name_350_);
if (lean_obj_tag(v___x_364_) == 1)
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_552_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_552_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_552_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_552_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_inc(v_val_365_);
v___x_369_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_365_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
v___x_370_ = l_Lean_Environment_Replay_x27_replayConstants(v___x_369_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_550_; 
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_551_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_550_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_550_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v_pending_375_; uint8_t v___x_376_; lean_object* v_a_378_; lean_object* v___y_393_; 
v___x_374_ = lean_st_ref_get(v_a_352_);
v_pending_375_ = lean_ctor_get(v___x_374_, 2);
lean_inc(v_pending_375_);
lean_dec(v___x_374_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_350_, v_pending_375_);
lean_dec(v_pending_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_406_; 
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_val_365_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_name_350_);
v___x_404_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_404_);
v___x_406_ = v___x_357_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v___f_408_; 
lean_inc(v_name_350_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(v___f_408_, 0, v_name_350_);
switch(lean_obj_tag(v_val_365_))
{
case 0:
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_409_ = lean_ctor_get(v_val_365_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_val_365_);
if (v_isSharedCheck_420_ == 0)
{
v___x_411_ = v_val_365_;
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v_val_365_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_val_409_);
v___x_414_ = v_reuseFailAlloc_419_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_414_, v_a_352_);
lean_dec_ref(v___x_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v___x_417_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v_a_416_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_417_;
goto v___jp_392_;
}
else
{
lean_object* v_a_418_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_418_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v___x_415_);
v_a_378_ = v_a_418_;
goto v___jp_377_;
}
}
}
}
case 1:
{
lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_421_ = lean_ctor_get(v_val_365_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_val_365_);
if (v_isSharedCheck_432_ == 0)
{
v___x_423_ = v_val_365_;
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_val_365_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_432_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_val_421_);
v___x_426_ = v_reuseFailAlloc_431_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_426_, v_a_352_);
lean_dec_ref(v___x_426_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref(v___x_427_);
v___x_429_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v_a_428_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_429_;
goto v___jp_392_;
}
else
{
lean_object* v_a_430_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_430_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_427_);
v_a_378_ = v_a_430_;
goto v___jp_377_;
}
}
}
}
case 2:
{
lean_object* v_val_433_; lean_object* v___x_434_; lean_object* v_env_435_; lean_object* v___f_436_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_val_433_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_val_433_);
v___x_434_ = lean_st_ref_get(v_a_352_);
v_env_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_ref(v_env_435_);
lean_dec(v___x_434_);
lean_inc_ref(v___f_408_);
lean_inc_ref(v_val_433_);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_Environment_Replay_x27_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(v___f_436_, 0, v_val_433_);
lean_closure_set(v___f_436_, 1, v___f_408_);
v___x_440_ = l_Lean_ConstantInfo_name(v_val_365_);
lean_dec_ref(v_val_365_);
v___x_441_ = lean_environment_find(v_env_435_, v___x_440_);
if (lean_obj_tag(v___x_441_) == 1)
{
lean_object* v_val_442_; 
v_val_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_442_);
if (lean_obj_tag(v_val_442_) == 2)
{
lean_object* v_toConstantVal_443_; lean_object* v_val_444_; lean_object* v_toConstantVal_445_; lean_object* v_all_446_; lean_object* v_name_447_; lean_object* v_levelParams_448_; lean_object* v_type_449_; lean_object* v_all_450_; lean_object* v_name_451_; lean_object* v_levelParams_452_; lean_object* v_type_453_; uint8_t v___y_455_; uint8_t v___x_462_; 
lean_dec_ref(v___x_441_);
lean_dec_ref(v___f_436_);
v_toConstantVal_443_ = lean_ctor_get(v_val_433_, 0);
v_val_444_ = lean_ctor_get(v_val_442_, 0);
lean_inc_ref(v_val_444_);
lean_dec_ref(v_val_442_);
v_toConstantVal_445_ = lean_ctor_get(v_val_444_, 0);
lean_inc_ref(v_toConstantVal_445_);
v_all_446_ = lean_ctor_get(v_val_433_, 2);
v_name_447_ = lean_ctor_get(v_toConstantVal_443_, 0);
v_levelParams_448_ = lean_ctor_get(v_toConstantVal_443_, 1);
v_type_449_ = lean_ctor_get(v_toConstantVal_443_, 2);
v_all_450_ = lean_ctor_get(v_val_444_, 2);
lean_inc(v_all_450_);
lean_dec_ref(v_val_444_);
v_name_451_ = lean_ctor_get(v_toConstantVal_445_, 0);
lean_inc(v_name_451_);
v_levelParams_452_ = lean_ctor_get(v_toConstantVal_445_, 1);
lean_inc(v_levelParams_452_);
v_type_453_ = lean_ctor_get(v_toConstantVal_445_, 2);
lean_inc_ref(v_type_453_);
lean_dec_ref(v_toConstantVal_445_);
v___x_462_ = lean_name_eq(v_name_447_, v_name_451_);
lean_dec(v_name_451_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_type_453_);
v___y_455_ = v___x_462_;
goto v___jp_454_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = lean_expr_eqv(v_type_449_, v_type_453_);
lean_dec_ref(v_type_453_);
v___y_455_ = v___x_463_;
goto v___jp_454_;
}
v___jp_454_:
{
if (v___y_455_ == 0)
{
lean_dec(v_levelParams_452_);
lean_dec(v_all_450_);
lean_del_object(v___x_357_);
goto v___jp_437_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_levelParams_448_, v_levelParams_452_);
lean_dec(v_levelParams_452_);
if (v___x_456_ == 0)
{
lean_dec(v_all_450_);
lean_del_object(v___x_357_);
goto v___jp_437_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_all_446_, v_all_450_);
lean_dec(v_all_450_);
if (v___x_457_ == 0)
{
lean_del_object(v___x_357_);
goto v___jp_437_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec_ref(v_val_433_);
lean_dec_ref(v___f_408_);
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_name_350_);
v___x_458_ = lean_box(0);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_458_);
v___x_460_ = v___x_357_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_val_442_);
lean_dec_ref(v_val_433_);
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v___x_464_ = l_Lean_Environment_Replay_x27_replayConstant___lam__2(v___f_436_, v___x_441_, v_a_351_, v_a_352_);
lean_dec_ref(v___x_441_);
v___y_393_ = v___x_464_;
goto v___jp_392_;
}
}
else
{
lean_object* v___x_465_; 
lean_dec_ref(v_val_433_);
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v___x_465_ = l_Lean_Environment_Replay_x27_replayConstant___lam__2(v___f_436_, v___x_441_, v_a_351_, v_a_352_);
lean_dec(v___x_441_);
v___y_393_ = v___x_465_;
goto v___jp_392_;
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_Environment_Replay_x27_replayConstant___lam__1(v_val_433_, v___f_408_, v___x_438_, v_a_351_, v_a_352_);
v___y_393_ = v___x_439_;
goto v___jp_392_;
}
}
case 3:
{
lean_object* v_val_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_466_ = lean_ctor_get(v_val_365_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_val_365_);
if (v_isSharedCheck_477_ == 0)
{
v___x_468_ = v_val_365_;
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_val_466_);
lean_dec(v_val_365_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_val_466_);
v___x_471_ = v_reuseFailAlloc_476_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_471_, v_a_352_);
lean_dec_ref(v___x_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
v___x_474_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v_a_473_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_474_;
goto v___jp_392_;
}
else
{
lean_object* v_a_475_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_475_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v___x_472_);
v_a_378_ = v_a_475_;
goto v___jp_377_;
}
}
}
}
case 4:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v_val_365_);
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v___x_478_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__3));
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
v___x_479_ = l_Lean_Environment_Replay_x27_replayConstant(v___x_478_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref(v___x_479_);
v___x_480_ = lean_box(4);
v___x_481_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_480_, v_a_352_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_483_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
v___x_483_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v_a_482_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_483_;
goto v___jp_392_;
}
else
{
lean_object* v_a_484_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_484_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_481_);
v_a_378_ = v_a_484_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_485_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_485_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_479_);
v_a_378_ = v_a_485_;
goto v___jp_377_;
}
}
case 5:
{
lean_object* v_val_486_; lean_object* v_toConstantVal_487_; lean_object* v_numParams_488_; lean_object* v_all_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_486_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_val_486_);
lean_dec_ref(v_val_365_);
v_toConstantVal_487_ = lean_ctor_get(v_val_486_, 0);
lean_inc_ref(v_toConstantVal_487_);
v_numParams_488_ = lean_ctor_get(v_val_486_, 1);
lean_inc(v_numParams_488_);
v_all_489_ = lean_ctor_get(v_val_486_, 3);
lean_inc(v_all_489_);
lean_dec_ref(v_val_486_);
v___x_490_ = lean_box(0);
v___x_491_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(v_all_489_, v___x_490_, v_a_351_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v___x_493_ = lean_box(0);
v___x_494_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(v_a_492_, v___x_493_, v_a_352_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v___x_494_);
v___x_495_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__4(v_a_492_, v___x_490_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
lean_inc(v_a_496_);
v___x_497_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(v_a_496_, v___x_493_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_levelParams_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v___x_497_);
v_levelParams_498_ = lean_ctor_get(v_toConstantVal_487_, 1);
lean_inc(v_levelParams_498_);
lean_dec_ref(v_toConstantVal_487_);
v___x_499_ = l_List_mapTR_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__6(v_a_496_, v___x_490_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_501_, 0, v_levelParams_498_);
lean_ctor_set(v___x_501_, 1, v_numParams_488_);
lean_ctor_set(v___x_501_, 2, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*3, v___x_500_);
v___x_502_ = l_Lean_Environment_Replay_x27_addDecl___redArg(v___x_501_, v_a_352_);
lean_dec_ref(v___x_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v___x_504_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v_a_503_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_504_;
goto v___jp_392_;
}
else
{
lean_object* v_a_505_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_505_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_502_);
v_a_378_ = v_a_505_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_506_; 
lean_dec(v_a_496_);
lean_dec(v_numParams_488_);
lean_dec_ref(v_toConstantVal_487_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_506_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_497_);
v_a_378_ = v_a_506_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_507_; 
lean_dec(v_numParams_488_);
lean_dec_ref(v_toConstantVal_487_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_507_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_495_);
v_a_378_ = v_a_507_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_508_; 
lean_dec(v_a_492_);
lean_dec(v_numParams_488_);
lean_dec_ref(v_toConstantVal_487_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_508_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_494_);
v_a_378_ = v_a_508_;
goto v___jp_377_;
}
}
else
{
lean_object* v_a_509_; 
lean_dec(v_numParams_488_);
lean_dec_ref(v_toConstantVal_487_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v_a_509_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_491_);
v_a_378_ = v_a_509_;
goto v___jp_377_;
}
}
case 6:
{
lean_object* v_val_510_; lean_object* v___x_511_; lean_object* v_toConstantVal_512_; lean_object* v_env_513_; lean_object* v_remaining_514_; lean_object* v_pending_515_; lean_object* v_postponedConstructors_516_; lean_object* v_postponedRecursors_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_510_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_val_510_);
lean_dec_ref(v_val_365_);
v___x_511_ = lean_st_ref_take(v_a_352_);
v_toConstantVal_512_ = lean_ctor_get(v_val_510_, 0);
lean_inc_ref(v_toConstantVal_512_);
lean_dec_ref(v_val_510_);
v_env_513_ = lean_ctor_get(v___x_511_, 0);
v_remaining_514_ = lean_ctor_get(v___x_511_, 1);
v_pending_515_ = lean_ctor_get(v___x_511_, 2);
v_postponedConstructors_516_ = lean_ctor_get(v___x_511_, 3);
v_postponedRecursors_517_ = lean_ctor_get(v___x_511_, 4);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_529_ == 0)
{
v___x_519_ = v___x_511_;
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_postponedRecursors_517_);
lean_inc(v_postponedConstructors_516_);
lean_inc(v_pending_515_);
lean_inc(v_remaining_514_);
lean_inc(v_env_513_);
lean_dec(v___x_511_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_529_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_name_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v_name_521_ = lean_ctor_get(v_toConstantVal_512_, 0);
lean_inc(v_name_521_);
lean_dec_ref(v_toConstantVal_512_);
v___x_522_ = l_Lean_NameSet_insert(v_postponedConstructors_516_, v_name_521_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 3, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_env_513_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_remaining_514_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_pending_515_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_postponedRecursors_517_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_st_ref_set(v_a_352_, v___x_524_);
v___x_526_ = lean_box(0);
v___x_527_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v___x_526_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_527_;
goto v___jp_392_;
}
}
}
default: 
{
lean_object* v_val_530_; lean_object* v___x_531_; lean_object* v_toConstantVal_532_; lean_object* v_env_533_; lean_object* v_remaining_534_; lean_object* v_pending_535_; lean_object* v_postponedConstructors_536_; lean_object* v_postponedRecursors_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___f_408_);
lean_del_object(v___x_357_);
v_val_530_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_val_530_);
lean_dec_ref(v_val_365_);
v___x_531_ = lean_st_ref_take(v_a_352_);
v_toConstantVal_532_ = lean_ctor_get(v_val_530_, 0);
lean_inc_ref(v_toConstantVal_532_);
lean_dec_ref(v_val_530_);
v_env_533_ = lean_ctor_get(v___x_531_, 0);
v_remaining_534_ = lean_ctor_get(v___x_531_, 1);
v_pending_535_ = lean_ctor_get(v___x_531_, 2);
v_postponedConstructors_536_ = lean_ctor_get(v___x_531_, 3);
v_postponedRecursors_537_ = lean_ctor_get(v___x_531_, 4);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
v___x_539_ = v___x_531_;
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_postponedRecursors_537_);
lean_inc(v_postponedConstructors_536_);
lean_inc(v_pending_535_);
lean_inc(v_remaining_534_);
lean_inc(v_env_533_);
lean_dec(v___x_531_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_549_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_name_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v_name_541_ = lean_ctor_get(v_toConstantVal_532_, 0);
lean_inc(v_name_541_);
lean_dec_ref(v_toConstantVal_532_);
v___x_542_ = l_Lean_NameSet_insert(v_postponedRecursors_537_, v_name_541_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_env_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_remaining_534_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_pending_535_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_postponedConstructors_536_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v___x_542_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_st_ref_set(v_a_352_, v___x_544_);
v___x_546_ = lean_box(0);
v___x_547_ = l_Lean_Environment_Replay_x27_replayConstant___lam__0(v_name_350_, v___x_546_, v_a_351_, v_a_352_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
v___y_393_ = v___x_547_;
goto v___jp_392_;
}
}
}
}
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_379_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__0));
v___x_380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_350_, v___x_376_);
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = ((lean_object*)(l_Lean_Environment_Replay_x27_replayConstant___closed__1));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
v___x_384_ = lean_io_error_to_string(v_a_378_);
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
lean_dec_ref(v___x_384_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 18);
lean_ctor_set(v___x_367_, 0, v___x_385_);
v___x_387_ = v___x_367_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
lean_ctor_set(v___x_372_, 0, v___x_387_);
v___x_389_ = v___x_372_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
v___jp_392_:
{
if (lean_obj_tag(v___y_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
lean_del_object(v___x_372_);
lean_del_object(v___x_367_);
lean_dec(v_name_350_);
v_a_394_ = lean_ctor_get(v___y_393_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___y_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___y_393_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___y_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_a_398_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_a_398_);
lean_dec(v_a_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_a_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___y_393_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___y_393_);
v_a_378_ = v_a_403_;
goto v___jp_377_;
}
}
}
}
else
{
lean_del_object(v___x_367_);
lean_dec(v_val_365_);
lean_del_object(v___x_357_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_name_350_);
return v___x_370_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_364_);
lean_del_object(v___x_357_);
lean_dec(v_name_350_);
v___x_553_ = lean_obj_once(&l_Lean_Environment_Replay_x27_replayConstant___closed__7, &l_Lean_Environment_Replay_x27_replayConstant___closed__7_once, _init_l_Lean_Environment_Replay_x27_replayConstant___closed__7);
v___x_554_ = l_panic___at___00Lean_Environment_Replay_x27_replayConstant_spec__7(v___x_553_, v_a_351_, v_a_352_);
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
lean_dec(v_name_350_);
v_a_556_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_354_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_354_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(lean_object* v_init_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v_k_569_; lean_object* v_l_570_; lean_object* v_r_571_; lean_object* v___x_572_; 
v_k_569_ = lean_ctor_get(v_x_565_, 1);
lean_inc(v_k_569_);
v_l_570_ = lean_ctor_get(v_x_565_, 3);
lean_inc(v_l_570_);
v_r_571_ = lean_ctor_get(v_x_565_, 4);
lean_inc(v_r_571_);
lean_dec_ref(v_x_565_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_572_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(v_init_564_, v_l_570_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_573_; 
lean_dec_ref(v___x_572_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_573_ = l_Lean_Environment_Replay_x27_replayConstant(v_k_569_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; 
lean_dec_ref(v___x_573_);
v___x_574_ = lean_box(0);
v_init_564_ = v___x_574_;
v_x_565_ = v_r_571_;
goto _start;
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_r_571_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
v_a_576_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_573_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_dec(v_r_571_);
lean_dec(v_k_569_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v___x_572_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_init_564_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants(lean_object* v_names_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_box(0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(v___x_590_, v_names_586_, v_a_587_, v_a_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_599_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_590_);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_590_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstants___boxed(lean_object* v_names_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Environment_Replay_x27_replayConstants(v_names_608_, v_a_609_, v_a_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg___boxed(lean_object* v_as_x27_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(v_as_x27_613_, v_b_614_, v___y_615_, v___y_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg___boxed(lean_object* v_as_x27_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(v_as_x27_619_, v_b_620_, v___y_621_, v___y_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9___boxed(lean_object* v_init_625_, lean_object* v_x_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(v_init_625_, v_x_626_, v___y_627_, v___y_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_replayConstant___boxed(lean_object* v_name_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Environment_Replay_x27_replayConstant(v_name_631_, v_a_632_, v_a_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___redArg(v_x_636_, v_x_637_, v___y_638_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1___boxed(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_List_mapM_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__1(v_x_642_, v_x_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(lean_object* v_as_648_, lean_object* v_as_x27_649_, lean_object* v_b_650_, lean_object* v_a_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___redArg(v_as_x27_649_, v_b_650_, v___y_652_, v___y_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2___boxed(lean_object* v_as_656_, lean_object* v_as_x27_657_, lean_object* v_b_658_, lean_object* v_a_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__2(v_as_656_, v_as_x27_657_, v_b_658_, v_a_659_, v___y_660_, v___y_661_);
lean_dec(v_as_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(lean_object* v_as_664_, lean_object* v_as_x27_665_, lean_object* v_b_666_, lean_object* v_a_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___redArg(v_as_x27_665_, v_b_666_, v___y_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3___boxed(lean_object* v_as_672_, lean_object* v_as_x27_673_, lean_object* v_b_674_, lean_object* v_a_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__3(v_as_672_, v_as_x27_673_, v_b_674_, v_a_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v_as_x27_673_);
lean_dec(v_as_672_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(lean_object* v_as_680_, lean_object* v_as_x27_681_, lean_object* v_b_682_, lean_object* v_a_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___redArg(v_as_x27_681_, v_b_682_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5___boxed(lean_object* v_as_688_, lean_object* v_as_x27_689_, lean_object* v_b_690_, lean_object* v_a_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_List_forIn_x27_loop___at___00Lean_Environment_Replay_x27_replayConstant_spec__5(v_as_688_, v_as_x27_689_, v_b_690_, v_a_691_, v___y_692_, v___y_693_);
lean_dec(v_as_688_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(lean_object* v_init_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v_k_703_; lean_object* v_l_704_; lean_object* v_r_705_; lean_object* v___x_713_; 
v_k_703_ = lean_ctor_get(v_x_699_, 1);
lean_inc(v_k_703_);
v_l_704_ = lean_ctor_get(v_x_699_, 3);
lean_inc(v_l_704_);
v_r_705_ = lean_ctor_get(v_x_699_, 4);
lean_inc(v_r_705_);
lean_dec_ref(v_x_699_);
v___x_713_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(v_init_698_, v_l_704_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_743_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_742_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_742_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v_env_718_; lean_object* v___x_719_; 
v___x_717_ = lean_st_ref_get(v___y_701_);
v_env_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc_ref(v_env_718_);
lean_dec(v___x_717_);
lean_inc(v_k_703_);
v___x_719_ = lean_environment_find(v_env_718_, v_k_703_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v___x_719_);
if (lean_obj_tag(v_val_720_) == 6)
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v_val_720_, 0);
lean_inc_ref(v_val_721_);
lean_dec_ref(v_val_720_);
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v___y_700_, v_k_703_);
if (lean_obj_tag(v___x_722_) == 1)
{
lean_object* v_val_723_; 
v_val_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_723_);
lean_dec_ref(v___x_722_);
if (lean_obj_tag(v_val_723_) == 6)
{
lean_object* v_val_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_741_; 
v_val_724_ = lean_ctor_get(v_val_723_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_val_723_);
if (v_isSharedCheck_741_ == 0)
{
v___x_726_ = v_val_723_;
v_isShared_727_ = v_isSharedCheck_741_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_val_724_);
lean_dec(v_val_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_741_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_instBEqConstructorVal_beq(v_val_721_, v_val_724_);
lean_dec_ref(v_val_724_);
lean_dec_ref(v_val_721_);
if (v___x_728_ == 0)
{
uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_dec(v_r_705_);
v___x_729_ = 1;
v___x_730_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__1));
v___x_731_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_703_, v___x_729_);
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
lean_dec_ref(v___x_731_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 18);
lean_ctor_set(v___x_726_, 0, v___x_732_);
v___x_734_ = v___x_726_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 1);
lean_ctor_set(v___x_715_, 0, v___x_734_);
v___x_736_ = v___x_715_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v___x_739_; 
lean_del_object(v___x_726_);
lean_del_object(v___x_715_);
lean_dec(v_k_703_);
v___x_739_ = lean_box(0);
v_init_698_ = v___x_739_;
v_x_699_ = v_r_705_;
goto _start;
}
}
}
else
{
lean_dec(v_val_723_);
lean_dec_ref(v_val_721_);
lean_del_object(v___x_715_);
lean_dec(v_r_705_);
goto v___jp_706_;
}
}
else
{
lean_dec(v___x_722_);
lean_dec_ref(v_val_721_);
lean_del_object(v___x_715_);
lean_dec(v_r_705_);
goto v___jp_706_;
}
}
else
{
lean_dec(v_val_720_);
lean_del_object(v___x_715_);
lean_dec(v_r_705_);
goto v___jp_706_;
}
}
else
{
lean_dec(v___x_719_);
lean_del_object(v___x_715_);
lean_dec(v_r_705_);
goto v___jp_706_;
}
}
}
else
{
lean_dec(v_r_705_);
lean_dec(v_k_703_);
return v___x_713_;
}
v___jp_706_:
{
lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_707_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___closed__0));
v___x_708_ = 1;
v___x_709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_703_, v___x_708_);
v___x_710_ = lean_string_append(v___x_707_, v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_init_698_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0___boxed(lean_object* v_init_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(v_init_746_, v_x_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors(lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; lean_object* v_postponedConstructors_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_st_ref_get(v_a_753_);
v_postponedConstructors_756_ = lean_ctor_get(v___x_755_, 3);
lean_inc(v_postponedConstructors_756_);
lean_dec(v___x_755_);
v___x_757_ = lean_box(0);
v___x_758_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedConstructors_spec__0(v___x_757_, v_postponedConstructors_756_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_766_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_757_);
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_757_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
v_a_767_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_758_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_758_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedConstructors___boxed(lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Environment_Replay_x27_checkPostponedConstructors(v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(lean_object* v_init_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v_k_786_; lean_object* v_l_787_; lean_object* v_r_788_; lean_object* v___x_796_; 
v_k_786_ = lean_ctor_get(v_x_782_, 1);
lean_inc(v_k_786_);
v_l_787_ = lean_ctor_get(v_x_782_, 3);
lean_inc(v_l_787_);
v_r_788_ = lean_ctor_get(v_x_782_, 4);
lean_inc(v_r_788_);
lean_dec_ref(v_x_782_);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(v_init_781_, v_l_787_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_825_; 
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_826_);
v___x_798_ = v___x_796_;
v_isShared_799_ = v_isSharedCheck_825_;
goto v_resetjp_797_;
}
else
{
lean_dec(v___x_796_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_825_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v_env_801_; lean_object* v___x_802_; 
v___x_800_ = lean_st_ref_get(v___y_784_);
v_env_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc_ref(v_env_801_);
lean_dec(v___x_800_);
lean_inc(v_k_786_);
v___x_802_ = lean_environment_find(v_env_801_, v_k_786_);
if (lean_obj_tag(v___x_802_) == 1)
{
lean_object* v_val_803_; 
v_val_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref(v___x_802_);
if (lean_obj_tag(v_val_803_) == 7)
{
lean_object* v_val_804_; lean_object* v___x_805_; 
v_val_804_ = lean_ctor_get(v_val_803_, 0);
lean_inc_ref(v_val_804_);
lean_dec_ref(v_val_803_);
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v___y_783_, v_k_786_);
if (lean_obj_tag(v___x_805_) == 1)
{
lean_object* v_val_806_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_val_806_);
lean_dec_ref(v___x_805_);
if (lean_obj_tag(v_val_806_) == 7)
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_val_807_ = lean_ctor_get(v_val_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_val_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_809_ = v_val_806_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v_val_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_instBEqRecursorVal_beq(v_val_804_, v_val_807_);
lean_dec_ref(v_val_807_);
lean_dec_ref(v_val_804_);
if (v___x_811_ == 0)
{
uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_r_788_);
v___x_812_ = 1;
v___x_813_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__1));
v___x_814_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_786_, v___x_812_);
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
lean_dec_ref(v___x_814_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 18);
lean_ctor_set(v___x_809_, 0, v___x_815_);
v___x_817_ = v___x_809_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 1);
lean_ctor_set(v___x_798_, 0, v___x_817_);
v___x_819_ = v___x_798_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v___x_822_; 
lean_del_object(v___x_809_);
lean_del_object(v___x_798_);
lean_dec(v_k_786_);
v___x_822_ = lean_box(0);
v_init_781_ = v___x_822_;
v_x_782_ = v_r_788_;
goto _start;
}
}
}
else
{
lean_dec(v_val_806_);
lean_dec_ref(v_val_804_);
lean_del_object(v___x_798_);
lean_dec(v_r_788_);
goto v___jp_789_;
}
}
else
{
lean_dec(v___x_805_);
lean_dec_ref(v_val_804_);
lean_del_object(v___x_798_);
lean_dec(v_r_788_);
goto v___jp_789_;
}
}
else
{
lean_dec(v_val_803_);
lean_del_object(v___x_798_);
lean_dec(v_r_788_);
goto v___jp_789_;
}
}
else
{
lean_dec(v___x_802_);
lean_del_object(v___x_798_);
lean_dec(v_r_788_);
goto v___jp_789_;
}
}
}
else
{
lean_dec(v_r_788_);
lean_dec(v_k_786_);
return v___x_796_;
}
v___jp_789_:
{
lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_790_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___closed__0));
v___x_791_ = 1;
v___x_792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_786_, v___x_791_);
v___x_793_ = lean_string_append(v___x_790_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v_init_781_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0___boxed(lean_object* v_init_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(v_init_829_, v_x_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors(lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; lean_object* v_postponedRecursors_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = lean_st_ref_get(v_a_836_);
v_postponedRecursors_839_ = lean_ctor_get(v___x_838_, 4);
lean_inc(v_postponedRecursors_839_);
lean_dec(v___x_838_);
v___x_840_ = lean_box(0);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_checkPostponedRecursors_spec__0(v___x_840_, v_postponedRecursors_839_, v_a_835_, v_a_836_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_841_, 0);
lean_dec(v_unused_849_);
v___x_843_ = v___x_841_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_dec(v___x_841_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_840_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_840_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_841_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_841_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_x27_checkPostponedRecursors___boxed(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Environment_Replay_x27_checkPostponedRecursors(v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_inc(v_x_862_);
return v_x_862_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_key_864_ = lean_ctor_get(v_x_863_, 0);
v_value_865_ = lean_ctor_get(v_x_863_, 1);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v___x_867_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(v_x_862_, v_tail_866_);
lean_inc(v_value_865_);
lean_inc(v_key_864_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v_key_864_);
lean_ctor_set(v___x_868_, 1, v_value_865_);
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1___boxed(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(v_x_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec(v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(lean_object* v_as_873_, size_t v_i_874_, size_t v_stop_875_, lean_object* v_b_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_eq(v_i_874_, v_stop_875_);
if (v___x_877_ == 0)
{
size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_sub(v_i_874_, v___x_878_);
v___x_880_ = lean_array_uget_borrowed(v_as_873_, v___x_879_);
v___x_881_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Environment_replay_x27_spec__1(v_b_876_, v___x_880_);
lean_dec(v_b_876_);
v_i_874_ = v___x_879_;
v_b_876_ = v___x_881_;
goto _start;
}
else
{
return v_b_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2___boxed(lean_object* v_as_883_, lean_object* v_i_884_, lean_object* v_stop_885_, lean_object* v_b_886_){
_start:
{
size_t v_i_boxed_887_; size_t v_stop_boxed_888_; lean_object* v_res_889_; 
v_i_boxed_887_ = lean_unbox_usize(v_i_884_);
lean_dec(v_i_884_);
v_stop_boxed_888_ = lean_unbox_usize(v_stop_885_);
lean_dec(v_stop_885_);
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(v_as_883_, v_i_boxed_887_, v_stop_boxed_888_, v_b_886_);
lean_dec_ref(v_as_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(lean_object* v_as_x27_890_, lean_object* v_b_891_){
_start:
{
if (lean_obj_tag(v_as_x27_890_) == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_b_891_);
return v___x_893_;
}
else
{
lean_object* v_head_894_; lean_object* v_tail_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; uint8_t v___x_898_; 
v_head_894_ = lean_ctor_get(v_as_x27_890_, 0);
lean_inc(v_head_894_);
v_tail_895_ = lean_ctor_get(v_as_x27_890_, 1);
lean_inc(v_tail_895_);
lean_dec_ref(v_as_x27_890_);
v_fst_896_ = lean_ctor_get(v_head_894_, 0);
lean_inc(v_fst_896_);
v_snd_897_ = lean_ctor_get(v_head_894_, 1);
lean_inc(v_snd_897_);
lean_dec(v_head_894_);
v___x_898_ = l_Lean_ConstantInfo_isUnsafe(v_snd_897_);
if (v___x_898_ == 0)
{
uint8_t v___x_899_; 
v___x_899_ = l_Lean_ConstantInfo_isPartial(v_snd_897_);
lean_dec(v_snd_897_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_NameSet_insert(v_b_891_, v_fst_896_);
v_as_x27_890_ = v_tail_895_;
v_b_891_ = v___x_900_;
goto _start;
}
else
{
lean_dec(v_fst_896_);
v_as_x27_890_ = v_tail_895_;
goto _start;
}
}
else
{
lean_dec(v_snd_897_);
lean_dec(v_fst_896_);
v_as_x27_890_ = v_tail_895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg___boxed(lean_object* v_as_x27_904_, lean_object* v_b_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(v_as_x27_904_, v_b_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27(lean_object* v_newConstants_908_, lean_object* v_env_909_){
_start:
{
lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v_buckets_933_; lean_object* v_remaining_934_; lean_object* v___y_936_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_buckets_933_ = lean_ctor_get(v_newConstants_908_, 1);
v_remaining_934_ = lean_box(1);
v___x_954_ = lean_box(0);
v___x_955_ = lean_array_get_size(v_buckets_933_);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_nat_dec_lt(v___x_956_, v___x_955_);
if (v___x_957_ == 0)
{
v___y_936_ = v___x_954_;
goto v___jp_935_;
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_usize_of_nat(v___x_955_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Environment_replay_x27_spec__2(v_buckets_933_, v___x_958_, v___x_959_, v___x_954_);
v___y_936_ = v___x_960_;
goto v___jp_935_;
}
v___jp_911_:
{
if (lean_obj_tag(v___y_913_) == 0)
{
lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_923_; 
v_isSharedCheck_923_ = !lean_is_exclusive(v___y_913_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v___y_913_, 0);
lean_dec(v_unused_924_);
v___x_915_ = v___y_913_;
v_isShared_916_ = v_isSharedCheck_923_;
goto v_resetjp_914_;
}
else
{
lean_dec(v___y_913_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_923_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_917_ = lean_st_ref_get(v___y_912_);
lean_dec(v___y_912_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_919_ = lean_elab_environment_of_kernel_env(v_env_918_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_919_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v___y_912_);
v_a_925_ = lean_ctor_get(v___y_913_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___y_913_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___y_913_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___y_913_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_937_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(v___y_936_, v_remaining_934_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
v___x_939_ = lean_elab_environment_to_kernel_env(v_env_909_);
lean_inc(v_a_938_);
v___x_940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v_a_938_);
lean_ctor_set(v___x_940_, 2, v_remaining_934_);
lean_ctor_set(v___x_940_, 3, v_remaining_934_);
lean_ctor_set(v___x_940_, 4, v_remaining_934_);
v___x_941_ = lean_st_mk_ref(v___x_940_);
v___x_942_ = lean_box(0);
lean_inc(v___x_941_);
lean_inc_ref(v_newConstants_908_);
v___x_943_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Environment_Replay_x27_replayConstants_spec__9(v___x_942_, v_a_938_, v_newConstants_908_, v___x_941_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v___x_943_);
v___x_944_ = l_Lean_Environment_Replay_x27_checkPostponedConstructors(v_newConstants_908_, v___x_941_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_944_);
v___x_945_ = l_Lean_Environment_Replay_x27_checkPostponedRecursors(v_newConstants_908_, v___x_941_);
lean_dec_ref(v_newConstants_908_);
v___y_912_ = v___x_941_;
v___y_913_ = v___x_945_;
goto v___jp_911_;
}
else
{
lean_dec_ref(v_newConstants_908_);
v___y_912_ = v___x_941_;
v___y_913_ = v___x_944_;
goto v___jp_911_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___x_941_);
lean_dec_ref(v_newConstants_908_);
v_a_946_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_943_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay_x27___boxed(lean_object* v_newConstants_961_, lean_object* v_env_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Environment_replay_x27(v_newConstants_961_, v_env_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(lean_object* v_as_965_, lean_object* v_as_x27_966_, lean_object* v_b_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___redArg(v_as_x27_966_, v_b_967_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0___boxed(lean_object* v_as_971_, lean_object* v_as_x27_972_, lean_object* v_b_973_, lean_object* v_a_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_List_forIn_x27_loop___at___00Lean_Environment_replay_x27_spec__0(v_as_971_, v_as_x27_972_, v_b_973_, v_a_974_);
lean_dec(v_as_971_);
return v_res_976_;
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
