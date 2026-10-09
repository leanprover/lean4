// Lean compiler output
// Module: Lean.Replay
// Imports: import Lean.CoreM public import Lean.AddDecl import Lean.Util.FoldConsts
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
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Environment_ofKernelEnv(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1_spec__4(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':\n"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value;
static const lean_ctor_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Replay.0.Lean.Kernel.Environment.Replay.replayConstant"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Replay"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4_value;
static lean_once_cell_t l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "No such constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Invalid constructor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "No such recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid recursor "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_660_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_v_4_ = lean_ctor_get(v_t_2_, 2);
v_l_5_ = lean_ctor_get(v_t_2_, 3);
v_r_6_ = lean_ctor_get(v_t_2_, 4);
v_isSharedCheck_660_ = !lean_is_exclusive(v_t_2_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_t_2_, 0);
lean_dec(v_unused_661_);
v___x_8_ = v_t_2_;
v_isShared_9_ = v_isSharedCheck_660_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_r_6_);
lean_inc(v_l_5_);
lean_inc(v_v_4_);
lean_inc(v_k_3_);
lean_dec(v_t_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_660_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
uint8_t v___x_10_; 
v___x_10_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1_, v_k_3_);
switch(v___x_10_)
{
case 0:
{
lean_object* v_impl_11_; lean_object* v___x_12_; 
v_impl_11_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_k_1_, v_l_5_);
v___x_12_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_11_) == 0)
{
if (lean_obj_tag(v_r_6_) == 0)
{
lean_object* v_size_13_; lean_object* v_size_14_; lean_object* v_k_15_; lean_object* v_v_16_; lean_object* v_l_17_; lean_object* v_r_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v_size_13_ = lean_ctor_get(v_impl_11_, 0);
v_size_14_ = lean_ctor_get(v_r_6_, 0);
v_k_15_ = lean_ctor_get(v_r_6_, 1);
v_v_16_ = lean_ctor_get(v_r_6_, 2);
v_l_17_ = lean_ctor_get(v_r_6_, 3);
lean_inc(v_l_17_);
v_r_18_ = lean_ctor_get(v_r_6_, 4);
v___x_19_ = lean_unsigned_to_nat(3u);
v___x_20_ = lean_nat_mul(v___x_19_, v_size_13_);
v___x_21_ = lean_nat_dec_lt(v___x_20_, v_size_14_);
lean_dec(v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
lean_dec(v_l_17_);
v___x_22_ = lean_nat_add(v___x_12_, v_size_13_);
v___x_23_ = lean_nat_add(v___x_22_, v_size_14_);
lean_dec(v___x_22_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 3, v_impl_11_);
lean_ctor_set(v___x_8_, 0, v___x_23_);
v___x_25_ = v___x_8_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_26_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_26_, 3, v_impl_11_);
lean_ctor_set(v_reuseFailAlloc_26_, 4, v_r_6_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
else
{
lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_90_; 
lean_inc(v_r_18_);
lean_inc(v_v_16_);
lean_inc(v_k_15_);
lean_inc(v_size_14_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; lean_object* v_unused_92_; lean_object* v_unused_93_; lean_object* v_unused_94_; lean_object* v_unused_95_; 
v_unused_91_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_91_);
v_unused_92_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_92_);
v_unused_93_ = lean_ctor_get(v_r_6_, 2);
lean_dec(v_unused_93_);
v_unused_94_ = lean_ctor_get(v_r_6_, 1);
lean_dec(v_unused_94_);
v_unused_95_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_95_);
v___x_28_ = v_r_6_;
v_isShared_29_ = v_isSharedCheck_90_;
goto v_resetjp_27_;
}
else
{
lean_dec(v_r_6_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_90_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v_size_30_; lean_object* v_k_31_; lean_object* v_v_32_; lean_object* v_l_33_; lean_object* v_r_34_; lean_object* v_size_35_; lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; 
v_size_30_ = lean_ctor_get(v_l_17_, 0);
v_k_31_ = lean_ctor_get(v_l_17_, 1);
v_v_32_ = lean_ctor_get(v_l_17_, 2);
v_l_33_ = lean_ctor_get(v_l_17_, 3);
v_r_34_ = lean_ctor_get(v_l_17_, 4);
v_size_35_ = lean_ctor_get(v_r_18_, 0);
v___x_36_ = lean_unsigned_to_nat(2u);
v___x_37_ = lean_nat_mul(v___x_36_, v_size_35_);
v___x_38_ = lean_nat_dec_lt(v_size_30_, v___x_37_);
lean_dec(v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_66_; 
lean_inc(v_r_34_);
lean_inc(v_l_33_);
lean_inc(v_v_32_);
lean_inc(v_k_31_);
v_isSharedCheck_66_ = !lean_is_exclusive(v_l_17_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; lean_object* v_unused_68_; lean_object* v_unused_69_; lean_object* v_unused_70_; lean_object* v_unused_71_; 
v_unused_67_ = lean_ctor_get(v_l_17_, 4);
lean_dec(v_unused_67_);
v_unused_68_ = lean_ctor_get(v_l_17_, 3);
lean_dec(v_unused_68_);
v_unused_69_ = lean_ctor_get(v_l_17_, 2);
lean_dec(v_unused_69_);
v_unused_70_ = lean_ctor_get(v_l_17_, 1);
lean_dec(v_unused_70_);
v_unused_71_ = lean_ctor_get(v_l_17_, 0);
lean_dec(v_unused_71_);
v___x_40_ = v_l_17_;
v_isShared_41_ = v_isSharedCheck_66_;
goto v_resetjp_39_;
}
else
{
lean_dec(v_l_17_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_66_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___y_45_; lean_object* v___y_46_; lean_object* v___y_47_; lean_object* v___y_56_; 
v___x_42_ = lean_nat_add(v___x_12_, v_size_13_);
v___x_43_ = lean_nat_add(v___x_42_, v_size_14_);
lean_dec(v_size_14_);
if (lean_obj_tag(v_l_33_) == 0)
{
lean_object* v_size_64_; 
v_size_64_ = lean_ctor_get(v_l_33_, 0);
lean_inc(v_size_64_);
v___y_56_ = v_size_64_;
goto v___jp_55_;
}
else
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___y_56_ = v___x_65_;
goto v___jp_55_;
}
v___jp_44_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_nat_add(v___y_45_, v___y_47_);
lean_dec(v___y_47_);
lean_dec(v___y_45_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 4, v_r_18_);
lean_ctor_set(v___x_40_, 3, v_r_34_);
lean_ctor_set(v___x_40_, 2, v_v_16_);
lean_ctor_set(v___x_40_, 1, v_k_15_);
lean_ctor_set(v___x_40_, 0, v___x_48_);
v___x_50_ = v___x_40_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_k_15_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_v_16_);
lean_ctor_set(v_reuseFailAlloc_54_, 3, v_r_34_);
lean_ctor_set(v_reuseFailAlloc_54_, 4, v_r_18_);
v___x_50_ = v_reuseFailAlloc_54_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_52_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 4, v___x_50_);
lean_ctor_set(v___x_28_, 3, v___y_46_);
lean_ctor_set(v___x_28_, 2, v_v_32_);
lean_ctor_set(v___x_28_, 1, v_k_31_);
lean_ctor_set(v___x_28_, 0, v___x_43_);
v___x_52_ = v___x_28_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_k_31_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_v_32_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v___y_46_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
v___jp_55_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_nat_add(v___x_42_, v___y_56_);
lean_dec(v___y_56_);
lean_dec(v___x_42_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_l_33_);
lean_ctor_set(v___x_8_, 3, v_impl_11_);
lean_ctor_set(v___x_8_, 0, v___x_57_);
v___x_59_ = v___x_8_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_impl_11_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v_l_33_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; 
v___x_60_ = lean_nat_add(v___x_12_, v_size_35_);
if (lean_obj_tag(v_r_34_) == 0)
{
lean_object* v_size_61_; 
v_size_61_ = lean_ctor_get(v_r_34_, 0);
lean_inc(v_size_61_);
v___y_45_ = v___x_60_;
v___y_46_ = v___x_59_;
v___y_47_ = v_size_61_;
goto v___jp_44_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___y_45_ = v___x_60_;
v___y_46_ = v___x_59_;
v___y_47_ = v___x_62_;
goto v___jp_44_;
}
}
}
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
lean_del_object(v___x_8_);
v___x_72_ = lean_nat_add(v___x_12_, v_size_13_);
v___x_73_ = lean_nat_add(v___x_72_, v_size_14_);
lean_dec(v_size_14_);
v___x_74_ = lean_nat_add(v___x_72_, v_size_30_);
lean_dec(v___x_72_);
lean_inc_ref(v_impl_11_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 4, v_l_17_);
lean_ctor_set(v___x_28_, 3, v_impl_11_);
lean_ctor_set(v___x_28_, 2, v_v_4_);
lean_ctor_set(v___x_28_, 1, v_k_3_);
lean_ctor_set(v___x_28_, 0, v___x_74_);
v___x_76_ = v___x_28_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_89_, 3, v_impl_11_);
lean_ctor_set(v_reuseFailAlloc_89_, 4, v_l_17_);
v___x_76_ = v_reuseFailAlloc_89_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_isSharedCheck_83_ = !lean_is_exclusive(v_impl_11_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; lean_object* v_unused_85_; lean_object* v_unused_86_; lean_object* v_unused_87_; lean_object* v_unused_88_; 
v_unused_84_ = lean_ctor_get(v_impl_11_, 4);
lean_dec(v_unused_84_);
v_unused_85_ = lean_ctor_get(v_impl_11_, 3);
lean_dec(v_unused_85_);
v_unused_86_ = lean_ctor_get(v_impl_11_, 2);
lean_dec(v_unused_86_);
v_unused_87_ = lean_ctor_get(v_impl_11_, 1);
lean_dec(v_unused_87_);
v_unused_88_ = lean_ctor_get(v_impl_11_, 0);
lean_dec(v_unused_88_);
v___x_78_ = v_impl_11_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_dec(v_impl_11_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 4, v_r_18_);
lean_ctor_set(v___x_78_, 3, v___x_76_);
lean_ctor_set(v___x_78_, 2, v_v_16_);
lean_ctor_set(v___x_78_, 1, v_k_15_);
lean_ctor_set(v___x_78_, 0, v___x_73_);
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_k_15_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_v_16_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v_r_18_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v_size_96_ = lean_ctor_get(v_impl_11_, 0);
v___x_97_ = lean_nat_add(v___x_12_, v_size_96_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 3, v_impl_11_);
lean_ctor_set(v___x_8_, 0, v___x_97_);
v___x_99_ = v___x_8_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_impl_11_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v_r_6_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
if (lean_obj_tag(v_r_6_) == 0)
{
lean_object* v_l_101_; 
v_l_101_ = lean_ctor_get(v_r_6_, 3);
lean_inc(v_l_101_);
if (lean_obj_tag(v_l_101_) == 0)
{
lean_object* v_r_102_; 
v_r_102_ = lean_ctor_get(v_r_6_, 4);
lean_inc(v_r_102_);
if (lean_obj_tag(v_r_102_) == 0)
{
lean_object* v_size_103_; lean_object* v_k_104_; lean_object* v_v_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_118_; 
v_size_103_ = lean_ctor_get(v_r_6_, 0);
v_k_104_ = lean_ctor_get(v_r_6_, 1);
v_v_105_ = lean_ctor_get(v_r_6_, 2);
v_isSharedCheck_118_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; lean_object* v_unused_120_; 
v_unused_119_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_120_);
v___x_107_ = v_r_6_;
v_isShared_108_ = v_isSharedCheck_118_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_v_105_);
lean_inc(v_k_104_);
lean_inc(v_size_103_);
lean_dec(v_r_6_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_118_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_size_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v_size_109_ = lean_ctor_get(v_l_101_, 0);
v___x_110_ = lean_nat_add(v___x_12_, v_size_103_);
lean_dec(v_size_103_);
v___x_111_ = lean_nat_add(v___x_12_, v_size_109_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 4, v_l_101_);
lean_ctor_set(v___x_107_, 3, v_impl_11_);
lean_ctor_set(v___x_107_, 2, v_v_4_);
lean_ctor_set(v___x_107_, 1, v_k_3_);
lean_ctor_set(v___x_107_, 0, v___x_111_);
v___x_113_ = v___x_107_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_impl_11_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v_l_101_);
v___x_113_ = v_reuseFailAlloc_117_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_r_102_);
lean_ctor_set(v___x_8_, 3, v___x_113_);
lean_ctor_set(v___x_8_, 2, v_v_105_);
lean_ctor_set(v___x_8_, 1, v_k_104_);
lean_ctor_set(v___x_8_, 0, v___x_110_);
v___x_115_ = v___x_8_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_r_102_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_k_121_; lean_object* v_v_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_145_; 
v_k_121_ = lean_ctor_get(v_r_6_, 1);
v_v_122_ = lean_ctor_get(v_r_6_, 2);
v_isSharedCheck_145_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; lean_object* v_unused_147_; lean_object* v_unused_148_; 
v_unused_146_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_146_);
v_unused_147_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_147_);
v_unused_148_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_148_);
v___x_124_ = v_r_6_;
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_v_122_);
lean_inc(v_k_121_);
lean_dec(v_r_6_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_k_126_; lean_object* v_v_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_141_; 
v_k_126_ = lean_ctor_get(v_l_101_, 1);
v_v_127_ = lean_ctor_get(v_l_101_, 2);
v_isSharedCheck_141_ = !lean_is_exclusive(v_l_101_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; lean_object* v_unused_143_; lean_object* v_unused_144_; 
v_unused_142_ = lean_ctor_get(v_l_101_, 4);
lean_dec(v_unused_142_);
v_unused_143_ = lean_ctor_get(v_l_101_, 3);
lean_dec(v_unused_143_);
v_unused_144_ = lean_ctor_get(v_l_101_, 0);
lean_dec(v_unused_144_);
v___x_129_ = v_l_101_;
v_isShared_130_ = v_isSharedCheck_141_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_v_127_);
lean_inc(v_k_126_);
lean_dec(v_l_101_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_141_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_unsigned_to_nat(3u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_102_);
lean_ctor_set(v___x_129_, 3, v_r_102_);
lean_ctor_set(v___x_129_, 2, v_v_4_);
lean_ctor_set(v___x_129_, 1, v_k_3_);
lean_ctor_set(v___x_129_, 0, v___x_12_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_r_102_);
v___x_133_ = v_reuseFailAlloc_140_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 3, v_r_102_);
lean_ctor_set(v___x_124_, 0, v___x_12_);
v___x_135_ = v___x_124_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_k_121_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_v_122_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v_r_102_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v___x_135_);
lean_ctor_set(v___x_8_, 3, v___x_133_);
lean_ctor_set(v___x_8_, 2, v_v_127_);
lean_ctor_set(v___x_8_, 1, v_k_126_);
lean_ctor_set(v___x_8_, 0, v___x_131_);
v___x_137_ = v___x_8_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_k_126_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_149_; 
v_r_149_ = lean_ctor_get(v_r_6_, 4);
lean_inc(v_r_149_);
if (lean_obj_tag(v_r_149_) == 0)
{
lean_object* v_k_150_; lean_object* v_v_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_162_; 
v_k_150_ = lean_ctor_get(v_r_6_, 1);
v_v_151_ = lean_ctor_get(v_r_6_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; 
v_unused_163_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_165_);
v___x_153_ = v_r_6_;
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_v_151_);
lean_inc(v_k_150_);
lean_dec(v_r_6_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(3u);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v_l_101_);
lean_ctor_set(v___x_153_, 2, v_v_4_);
lean_ctor_set(v___x_153_, 1, v_k_3_);
lean_ctor_set(v___x_153_, 0, v___x_12_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_161_, 4, v_l_101_);
v___x_157_ = v_reuseFailAlloc_161_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_r_149_);
lean_ctor_set(v___x_8_, 3, v___x_157_);
lean_ctor_set(v___x_8_, 2, v_v_151_);
lean_ctor_set(v___x_8_, 1, v_k_150_);
lean_ctor_set(v___x_8_, 0, v___x_155_);
v___x_159_ = v___x_8_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_150_);
lean_ctor_set(v_reuseFailAlloc_160_, 2, v_v_151_);
lean_ctor_set(v_reuseFailAlloc_160_, 3, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_160_, 4, v_r_149_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_size_166_; lean_object* v_k_167_; lean_object* v_v_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
v_size_166_ = lean_ctor_get(v_r_6_, 0);
v_k_167_ = lean_ctor_get(v_r_6_, 1);
v_v_168_ = lean_ctor_get(v_r_6_, 2);
v_isSharedCheck_179_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_180_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_181_);
v___x_170_ = v_r_6_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_v_168_);
lean_inc(v_k_167_);
lean_inc(v_size_166_);
lean_dec(v_r_6_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 3, v_r_149_);
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_size_166_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_167_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_v_168_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_r_149_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_r_149_);
v___x_173_ = v_reuseFailAlloc_178_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(2u);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v___x_173_);
lean_ctor_set(v___x_8_, 3, v_r_149_);
lean_ctor_set(v___x_8_, 0, v___x_174_);
v___x_176_ = v___x_8_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_r_149_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___x_173_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
else
{
lean_object* v___x_183_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 3, v_r_6_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_183_ = v___x_8_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_r_6_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_r_6_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
case 1:
{
lean_del_object(v___x_8_);
lean_dec(v_v_4_);
lean_dec(v_k_3_);
if (lean_obj_tag(v_l_5_) == 0)
{
if (lean_obj_tag(v_r_6_) == 0)
{
lean_object* v_size_185_; lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v_l_188_; lean_object* v_r_189_; lean_object* v_size_190_; lean_object* v_k_191_; lean_object* v_v_192_; lean_object* v_l_193_; lean_object* v_r_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_size_185_ = lean_ctor_get(v_l_5_, 0);
v_k_186_ = lean_ctor_get(v_l_5_, 1);
v_v_187_ = lean_ctor_get(v_l_5_, 2);
v_l_188_ = lean_ctor_get(v_l_5_, 3);
v_r_189_ = lean_ctor_get(v_l_5_, 4);
lean_inc(v_r_189_);
v_size_190_ = lean_ctor_get(v_r_6_, 0);
v_k_191_ = lean_ctor_get(v_r_6_, 1);
v_v_192_ = lean_ctor_get(v_r_6_, 2);
v_l_193_ = lean_ctor_get(v_r_6_, 3);
lean_inc(v_l_193_);
v_r_194_ = lean_ctor_get(v_r_6_, 4);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_dec_lt(v_size_185_, v_size_190_);
if (v___x_196_ == 0)
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_332_; 
lean_inc(v_l_188_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; lean_object* v_unused_337_; 
v_unused_333_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_l_5_, 2);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_l_5_, 1);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_337_);
v___x_198_ = v_l_5_;
v_isShared_199_ = v_isSharedCheck_332_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_l_5_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_332_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v_tree_201_; 
v___x_200_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_186_, v_v_187_, v_l_188_, v_r_189_);
v_tree_201_ = lean_ctor_get(v___x_200_, 2);
if (lean_obj_tag(v_tree_201_) == 0)
{
lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v_size_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
lean_inc_ref(v_tree_201_);
v_k_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_k_202_);
v_v_203_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_v_203_);
lean_dec_ref(v___x_200_);
v_size_204_ = lean_ctor_get(v_tree_201_, 0);
v___x_205_ = lean_unsigned_to_nat(3u);
v___x_206_ = lean_nat_mul(v___x_205_, v_size_204_);
v___x_207_ = lean_nat_dec_lt(v___x_206_, v_size_190_);
lean_dec(v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
lean_dec(v_l_193_);
v___x_208_ = lean_nat_add(v___x_195_, v_size_204_);
v___x_209_ = lean_nat_add(v___x_208_, v_size_190_);
lean_dec(v___x_208_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_r_6_);
lean_ctor_set(v___x_198_, 3, v_tree_201_);
lean_ctor_set(v___x_198_, 2, v_v_203_);
lean_ctor_set(v___x_198_, 1, v_k_202_);
lean_ctor_set(v___x_198_, 0, v___x_209_);
v___x_211_ = v___x_198_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_tree_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_6_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_267_; 
lean_inc(v_r_194_);
lean_inc(v_v_192_);
lean_inc(v_k_191_);
lean_inc(v_size_190_);
v_isSharedCheck_267_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_268_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_r_6_, 2);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_r_6_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_272_);
v___x_214_ = v_r_6_;
v_isShared_215_ = v_isSharedCheck_267_;
goto v_resetjp_213_;
}
else
{
lean_dec(v_r_6_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_267_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_size_216_; lean_object* v_k_217_; lean_object* v_v_218_; lean_object* v_l_219_; lean_object* v_r_220_; lean_object* v_size_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_size_216_ = lean_ctor_get(v_l_193_, 0);
v_k_217_ = lean_ctor_get(v_l_193_, 1);
v_v_218_ = lean_ctor_get(v_l_193_, 2);
v_l_219_ = lean_ctor_get(v_l_193_, 3);
v_r_220_ = lean_ctor_get(v_l_193_, 4);
v_size_221_ = lean_ctor_get(v_r_194_, 0);
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = lean_nat_mul(v___x_222_, v_size_221_);
v___x_224_ = lean_nat_dec_lt(v_size_216_, v___x_223_);
lean_dec(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_252_; 
lean_inc(v_r_220_);
lean_inc(v_l_219_);
lean_inc(v_v_218_);
lean_inc(v_k_217_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_l_193_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; 
v_unused_253_ = lean_ctor_get(v_l_193_, 4);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_l_193_, 3);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_l_193_, 2);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_l_193_, 1);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_l_193_, 0);
lean_dec(v_unused_257_);
v___x_226_ = v_l_193_;
v_isShared_227_ = v_isSharedCheck_252_;
goto v_resetjp_225_;
}
else
{
lean_dec(v_l_193_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_252_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_242_; 
v___x_228_ = lean_nat_add(v___x_195_, v_size_204_);
v___x_229_ = lean_nat_add(v___x_228_, v_size_190_);
lean_dec(v_size_190_);
if (lean_obj_tag(v_l_219_) == 0)
{
lean_object* v_size_250_; 
v_size_250_ = lean_ctor_get(v_l_219_, 0);
lean_inc(v_size_250_);
v___y_242_ = v_size_250_;
goto v___jp_241_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___y_242_ = v___x_251_;
goto v___jp_241_;
}
v___jp_230_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_nat_add(v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec(v___y_232_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 4, v_r_194_);
lean_ctor_set(v___x_226_, 3, v_r_220_);
lean_ctor_set(v___x_226_, 2, v_v_192_);
lean_ctor_set(v___x_226_, 1, v_k_191_);
lean_ctor_set(v___x_226_, 0, v___x_234_);
v___x_236_ = v___x_226_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_r_220_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_r_194_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v___x_236_);
lean_ctor_set(v___x_214_, 3, v___y_231_);
lean_ctor_set(v___x_214_, 2, v_v_218_);
lean_ctor_set(v___x_214_, 1, v_k_217_);
lean_ctor_set(v___x_214_, 0, v___x_229_);
v___x_238_ = v___x_214_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_217_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_218_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v___y_231_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_nat_add(v___x_228_, v___y_242_);
lean_dec(v___y_242_);
lean_dec(v___x_228_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_l_219_);
lean_ctor_set(v___x_198_, 3, v_tree_201_);
lean_ctor_set(v___x_198_, 2, v_v_203_);
lean_ctor_set(v___x_198_, 1, v_k_202_);
lean_ctor_set(v___x_198_, 0, v___x_243_);
v___x_245_ = v___x_198_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_tree_201_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_l_219_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
v___x_246_ = lean_nat_add(v___x_195_, v_size_221_);
if (lean_obj_tag(v_r_220_) == 0)
{
lean_object* v_size_247_; 
v_size_247_ = lean_ctor_get(v_r_220_, 0);
lean_inc(v_size_247_);
v___y_231_ = v___x_245_;
v___y_232_ = v___x_246_;
v___y_233_ = v_size_247_;
goto v___jp_230_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___y_231_ = v___x_245_;
v___y_232_ = v___x_246_;
v___y_233_ = v___x_248_;
goto v___jp_230_;
}
}
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_258_ = lean_nat_add(v___x_195_, v_size_204_);
v___x_259_ = lean_nat_add(v___x_258_, v_size_190_);
lean_dec(v_size_190_);
v___x_260_ = lean_nat_add(v___x_258_, v_size_216_);
lean_dec(v___x_258_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v_l_193_);
lean_ctor_set(v___x_214_, 3, v_tree_201_);
lean_ctor_set(v___x_214_, 2, v_v_203_);
lean_ctor_set(v___x_214_, 1, v_k_202_);
lean_ctor_set(v___x_214_, 0, v___x_260_);
v___x_262_ = v___x_214_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_tree_201_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_l_193_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_r_194_);
lean_ctor_set(v___x_198_, 3, v___x_262_);
lean_ctor_set(v___x_198_, 2, v_v_192_);
lean_ctor_set(v___x_198_, 1, v_k_191_);
lean_ctor_set(v___x_198_, 0, v___x_259_);
v___x_264_ = v___x_198_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_265_, 3, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 4, v_r_194_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
else
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_326_; 
lean_inc(v_r_194_);
lean_inc(v_v_192_);
lean_inc(v_k_191_);
lean_inc(v_size_190_);
v_isSharedCheck_326_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_327_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_r_6_, 2);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_r_6_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_331_);
v___x_274_ = v_r_6_;
v_isShared_275_ = v_isSharedCheck_326_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_r_6_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_326_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
if (lean_obj_tag(v_l_193_) == 0)
{
if (lean_obj_tag(v_r_194_) == 0)
{
lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v_size_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_inc(v_tree_201_);
v_k_276_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_k_276_);
v_v_277_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_v_277_);
lean_dec_ref(v___x_200_);
v_size_278_ = lean_ctor_get(v_l_193_, 0);
v___x_279_ = lean_nat_add(v___x_195_, v_size_190_);
lean_dec(v_size_190_);
v___x_280_ = lean_nat_add(v___x_195_, v_size_278_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v_l_193_);
lean_ctor_set(v___x_274_, 3, v_tree_201_);
lean_ctor_set(v___x_274_, 2, v_v_277_);
lean_ctor_set(v___x_274_, 1, v_k_276_);
lean_ctor_set(v___x_274_, 0, v___x_280_);
v___x_282_ = v___x_274_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_tree_201_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_l_193_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_r_194_);
lean_ctor_set(v___x_198_, 3, v___x_282_);
lean_ctor_set(v___x_198_, 2, v_v_192_);
lean_ctor_set(v___x_198_, 1, v_k_191_);
lean_ctor_set(v___x_198_, 0, v___x_279_);
v___x_284_ = v___x_198_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_r_194_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_k_287_; lean_object* v_v_288_; lean_object* v_k_289_; lean_object* v_v_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_size_190_);
v_k_287_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_k_287_);
v_v_288_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_v_288_);
lean_dec_ref(v___x_200_);
v_k_289_ = lean_ctor_get(v_l_193_, 1);
v_v_290_ = lean_ctor_get(v_l_193_, 2);
v_isSharedCheck_304_ = !lean_is_exclusive(v_l_193_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; 
v_unused_305_ = lean_ctor_get(v_l_193_, 4);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_l_193_, 3);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_l_193_, 0);
lean_dec(v_unused_307_);
v___x_292_ = v_l_193_;
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_v_290_);
lean_inc(v_k_289_);
lean_dec(v_l_193_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(3u);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 4, v_r_194_);
lean_ctor_set(v___x_292_, 3, v_r_194_);
lean_ctor_set(v___x_292_, 2, v_v_288_);
lean_ctor_set(v___x_292_, 1, v_k_287_);
lean_ctor_set(v___x_292_, 0, v___x_195_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_k_287_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_v_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_r_194_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_r_194_);
v___x_296_ = v_reuseFailAlloc_303_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 3, v_r_194_);
lean_ctor_set(v___x_274_, 0, v___x_195_);
v___x_298_ = v___x_274_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_r_194_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_r_194_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v___x_298_);
lean_ctor_set(v___x_198_, 3, v___x_296_);
lean_ctor_set(v___x_198_, 2, v_v_290_);
lean_ctor_set(v___x_198_, 1, v_k_289_);
lean_ctor_set(v___x_198_, 0, v___x_294_);
v___x_300_ = v___x_198_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_v_290_);
lean_ctor_set(v_reuseFailAlloc_301_, 3, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_301_, 4, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_194_) == 0)
{
lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_size_190_);
v_k_308_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_k_308_);
v_v_309_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_v_309_);
lean_dec_ref(v___x_200_);
v___x_310_ = lean_unsigned_to_nat(3u);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v_l_193_);
lean_ctor_set(v___x_274_, 2, v_v_309_);
lean_ctor_set(v___x_274_, 1, v_k_308_);
lean_ctor_set(v___x_274_, 0, v___x_195_);
v___x_312_ = v___x_274_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_l_193_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_l_193_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_r_194_);
lean_ctor_set(v___x_198_, 3, v___x_312_);
lean_ctor_set(v___x_198_, 2, v_v_192_);
lean_ctor_set(v___x_198_, 1, v_k_191_);
lean_ctor_set(v___x_198_, 0, v___x_310_);
v___x_314_ = v___x_198_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_r_194_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v___x_320_; 
v_k_317_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_k_317_);
v_v_318_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_v_318_);
lean_dec_ref(v___x_200_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 3, v_r_194_);
v___x_320_ = v___x_274_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_size_190_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_r_194_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_r_194_);
v___x_320_ = v_reuseFailAlloc_325_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(2u);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v___x_320_);
lean_ctor_set(v___x_198_, 3, v_r_194_);
lean_ctor_set(v___x_198_, 2, v_v_318_);
lean_ctor_set(v___x_198_, 1, v_k_317_);
lean_ctor_set(v___x_198_, 0, v___x_321_);
v___x_323_ = v___x_198_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_r_194_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v___x_320_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_490_; 
lean_inc(v_r_194_);
lean_inc(v_v_192_);
lean_inc(v_k_191_);
v_isSharedCheck_490_ = !lean_is_exclusive(v_r_6_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_491_ = lean_ctor_get(v_r_6_, 4);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_r_6_, 3);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_r_6_, 2);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_r_6_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_r_6_, 0);
lean_dec(v_unused_495_);
v___x_339_ = v_r_6_;
v_isShared_340_ = v_isSharedCheck_490_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_r_6_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_490_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v_tree_342_; 
v___x_341_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_191_, v_v_192_, v_l_193_, v_r_194_);
v_tree_342_ = lean_ctor_get(v___x_341_, 2);
lean_inc(v_tree_342_);
if (lean_obj_tag(v_tree_342_) == 0)
{
lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v_size_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_k_343_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_k_343_);
v_v_344_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_v_344_);
lean_dec_ref(v___x_341_);
v_size_345_ = lean_ctor_get(v_tree_342_, 0);
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = lean_nat_mul(v___x_346_, v_size_345_);
v___x_348_ = lean_nat_dec_lt(v___x_347_, v_size_185_);
lean_dec(v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_dec(v_r_189_);
v___x_349_ = lean_nat_add(v___x_195_, v_size_185_);
v___x_350_ = lean_nat_add(v___x_349_, v_size_345_);
lean_dec(v___x_349_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_tree_342_);
lean_ctor_set(v___x_339_, 3, v_l_5_);
lean_ctor_set(v___x_339_, 2, v_v_344_);
lean_ctor_set(v___x_339_, 1, v_k_343_);
lean_ctor_set(v___x_339_, 0, v___x_350_);
v___x_352_ = v___x_339_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_tree_342_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
else
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_419_; 
lean_inc(v_l_188_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_inc(v_size_185_);
v_isSharedCheck_419_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; lean_object* v_unused_422_; lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_420_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_l_5_, 2);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v_l_5_, 1);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_424_);
v___x_355_ = v_l_5_;
v_isShared_356_ = v_isSharedCheck_419_;
goto v_resetjp_354_;
}
else
{
lean_dec(v_l_5_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_419_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_size_357_; lean_object* v_size_358_; lean_object* v_k_359_; lean_object* v_v_360_; lean_object* v_l_361_; lean_object* v_r_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_size_357_ = lean_ctor_get(v_l_188_, 0);
v_size_358_ = lean_ctor_get(v_r_189_, 0);
v_k_359_ = lean_ctor_get(v_r_189_, 1);
v_v_360_ = lean_ctor_get(v_r_189_, 2);
v_l_361_ = lean_ctor_get(v_r_189_, 3);
v_r_362_ = lean_ctor_get(v_r_189_, 4);
v___x_363_ = lean_unsigned_to_nat(2u);
v___x_364_ = lean_nat_mul(v___x_363_, v_size_357_);
v___x_365_ = lean_nat_dec_lt(v_size_358_, v___x_364_);
lean_dec(v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_403_; 
lean_inc(v_r_362_);
lean_inc(v_l_361_);
lean_inc(v_v_360_);
lean_inc(v_k_359_);
lean_del_object(v___x_355_);
v_isSharedCheck_403_ = !lean_is_exclusive(v_r_189_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_404_ = lean_ctor_get(v_r_189_, 4);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_r_189_, 3);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_r_189_, 2);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_r_189_, 1);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_r_189_, 0);
lean_dec(v_unused_408_);
v___x_367_ = v_r_189_;
v_isShared_368_ = v_isSharedCheck_403_;
goto v_resetjp_366_;
}
else
{
lean_dec(v_r_189_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_403_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___x_391_; lean_object* v___y_393_; 
v___x_369_ = lean_nat_add(v___x_195_, v_size_185_);
lean_dec(v_size_185_);
v___x_370_ = lean_nat_add(v___x_369_, v_size_345_);
lean_dec(v___x_369_);
v___x_391_ = lean_nat_add(v___x_195_, v_size_357_);
if (lean_obj_tag(v_l_361_) == 0)
{
lean_object* v_size_401_; 
v_size_401_ = lean_ctor_get(v_l_361_, 0);
lean_inc(v_size_401_);
v___y_393_ = v_size_401_;
goto v___jp_392_;
}
else
{
lean_object* v___x_402_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___y_393_ = v___x_402_;
goto v___jp_392_;
}
v___jp_371_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_nat_add(v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_inc_ref(v_tree_342_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_tree_342_);
lean_ctor_set(v___x_367_, 3, v_r_362_);
lean_ctor_set(v___x_367_, 2, v_v_344_);
lean_ctor_set(v___x_367_, 1, v_k_343_);
lean_ctor_set(v___x_367_, 0, v___x_375_);
v___x_377_ = v___x_367_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_r_362_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_tree_342_);
v___x_377_ = v_reuseFailAlloc_390_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_isSharedCheck_384_ = !lean_is_exclusive(v_tree_342_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; 
v_unused_385_ = lean_ctor_get(v_tree_342_, 4);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_tree_342_, 3);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_tree_342_, 2);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_tree_342_, 1);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_tree_342_, 0);
lean_dec(v_unused_389_);
v___x_379_ = v_tree_342_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_dec(v_tree_342_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 4, v___x_377_);
lean_ctor_set(v___x_379_, 3, v___y_372_);
lean_ctor_set(v___x_379_, 2, v_v_360_);
lean_ctor_set(v___x_379_, 1, v_k_359_);
lean_ctor_set(v___x_379_, 0, v___x_370_);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v___y_372_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v___x_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
v___jp_392_:
{
lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_394_ = lean_nat_add(v___x_391_, v___y_393_);
lean_dec(v___y_393_);
lean_dec(v___x_391_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_l_361_);
lean_ctor_set(v___x_339_, 3, v_l_188_);
lean_ctor_set(v___x_339_, 2, v_v_187_);
lean_ctor_set(v___x_339_, 1, v_k_186_);
lean_ctor_set(v___x_339_, 0, v___x_394_);
v___x_396_ = v___x_339_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_l_361_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = lean_nat_add(v___x_195_, v_size_345_);
if (lean_obj_tag(v_r_362_) == 0)
{
lean_object* v_size_398_; 
v_size_398_ = lean_ctor_get(v_r_362_, 0);
lean_inc(v_size_398_);
v___y_372_ = v___x_396_;
v___y_373_ = v___x_397_;
v___y_374_ = v_size_398_;
goto v___jp_371_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___y_372_ = v___x_396_;
v___y_373_ = v___x_397_;
v___y_374_ = v___x_399_;
goto v___jp_371_;
}
}
}
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_409_ = lean_nat_add(v___x_195_, v_size_185_);
lean_dec(v_size_185_);
v___x_410_ = lean_nat_add(v___x_409_, v_size_345_);
lean_dec(v___x_409_);
v___x_411_ = lean_nat_add(v___x_195_, v_size_345_);
v___x_412_ = lean_nat_add(v___x_411_, v_size_358_);
lean_dec(v___x_411_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_tree_342_);
lean_ctor_set(v___x_339_, 3, v_r_189_);
lean_ctor_set(v___x_339_, 2, v_v_344_);
lean_ctor_set(v___x_339_, 1, v_k_343_);
lean_ctor_set(v___x_339_, 0, v___x_412_);
v___x_414_ = v___x_339_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_tree_342_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 4, v___x_414_);
lean_ctor_set(v___x_355_, 0, v___x_410_);
v___x_416_ = v___x_355_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_188_) == 0)
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_448_; 
lean_inc_ref(v_l_188_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_inc(v_size_185_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; 
v_unused_449_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_l_5_, 2);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_l_5_, 1);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_453_);
v___x_426_ = v_l_5_;
v_isShared_427_ = v_isSharedCheck_448_;
goto v_resetjp_425_;
}
else
{
lean_dec(v_l_5_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_448_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
if (lean_obj_tag(v_r_189_) == 0)
{
lean_object* v_k_428_; lean_object* v_v_429_; lean_object* v_size_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v_k_428_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_k_428_);
v_v_429_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_v_429_);
lean_dec_ref(v___x_341_);
v_size_430_ = lean_ctor_get(v_r_189_, 0);
v___x_431_ = lean_nat_add(v___x_195_, v_size_185_);
lean_dec(v_size_185_);
v___x_432_ = lean_nat_add(v___x_195_, v_size_430_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_tree_342_);
lean_ctor_set(v___x_339_, 3, v_r_189_);
lean_ctor_set(v___x_339_, 2, v_v_429_);
lean_ctor_set(v___x_339_, 1, v_k_428_);
lean_ctor_set(v___x_339_, 0, v___x_432_);
v___x_434_ = v___x_339_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_k_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_v_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_tree_342_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 4, v___x_434_);
lean_ctor_set(v___x_426_, 0, v___x_431_);
v___x_436_ = v___x_426_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v_k_439_; lean_object* v_v_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec(v_size_185_);
v_k_439_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_k_439_);
v_v_440_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_v_440_);
lean_dec_ref(v___x_341_);
v___x_441_ = lean_unsigned_to_nat(3u);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_r_189_);
lean_ctor_set(v___x_339_, 3, v_r_189_);
lean_ctor_set(v___x_339_, 2, v_v_440_);
lean_ctor_set(v___x_339_, 1, v_k_439_);
lean_ctor_set(v___x_339_, 0, v___x_195_);
v___x_443_ = v___x_339_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_k_439_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_v_440_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_r_189_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_r_189_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 4, v___x_443_);
lean_ctor_set(v___x_426_, 0, v___x_441_);
v___x_445_ = v___x_426_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_189_) == 0)
{
lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_478_; 
lean_inc(v_l_188_);
lean_inc(v_v_187_);
lean_inc(v_k_186_);
v_isSharedCheck_478_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_479_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_l_5_, 2);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_l_5_, 1);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_483_);
v___x_455_ = v_l_5_;
v_isShared_456_ = v_isSharedCheck_478_;
goto v_resetjp_454_;
}
else
{
lean_dec(v_l_5_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_478_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_474_; 
v_k_457_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_k_457_);
v_v_458_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_v_458_);
lean_dec_ref(v___x_341_);
v_k_459_ = lean_ctor_get(v_r_189_, 1);
v_v_460_ = lean_ctor_get(v_r_189_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_r_189_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_475_ = lean_ctor_get(v_r_189_, 4);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_r_189_, 3);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_r_189_, 0);
lean_dec(v_unused_477_);
v___x_462_ = v_r_189_;
v_isShared_463_ = v_isSharedCheck_474_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_v_460_);
lean_inc(v_k_459_);
lean_dec(v_r_189_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_474_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(3u);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 4, v_l_188_);
lean_ctor_set(v___x_462_, 3, v_l_188_);
lean_ctor_set(v___x_462_, 2, v_v_187_);
lean_ctor_set(v___x_462_, 1, v_k_186_);
lean_ctor_set(v___x_462_, 0, v___x_195_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_l_188_);
v___x_466_ = v_reuseFailAlloc_473_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_l_188_);
lean_ctor_set(v___x_339_, 3, v_l_188_);
lean_ctor_set(v___x_339_, 2, v_v_458_);
lean_ctor_set(v___x_339_, 1, v_k_457_);
lean_ctor_set(v___x_339_, 0, v___x_195_);
v___x_468_ = v___x_339_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_k_457_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_l_188_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_l_188_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_468_);
lean_ctor_set(v___x_455_, 3, v___x_466_);
lean_ctor_set(v___x_455_, 2, v_v_460_);
lean_ctor_set(v___x_455_, 1, v_k_459_);
lean_ctor_set(v___x_455_, 0, v___x_464_);
v___x_470_ = v___x_455_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
else
{
lean_object* v_k_484_; lean_object* v_v_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v_k_484_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_k_484_);
v_v_485_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_v_485_);
lean_dec_ref(v___x_341_);
v___x_486_ = lean_unsigned_to_nat(2u);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_r_189_);
lean_ctor_set(v___x_339_, 3, v_l_5_);
lean_ctor_set(v___x_339_, 2, v_v_485_);
lean_ctor_set(v___x_339_, 1, v_k_484_);
lean_ctor_set(v___x_339_, 0, v___x_486_);
v___x_488_ = v___x_339_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_484_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_485_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_r_189_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
}
else
{
return v_l_5_;
}
}
else
{
return v_r_6_;
}
}
default: 
{
lean_object* v_impl_496_; lean_object* v___x_497_; 
v_impl_496_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_k_1_, v_r_6_);
v___x_497_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_496_) == 0)
{
if (lean_obj_tag(v_l_5_) == 0)
{
lean_object* v_size_498_; lean_object* v_size_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_l_502_; lean_object* v_r_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_size_498_ = lean_ctor_get(v_impl_496_, 0);
v_size_499_ = lean_ctor_get(v_l_5_, 0);
v_k_500_ = lean_ctor_get(v_l_5_, 1);
v_v_501_ = lean_ctor_get(v_l_5_, 2);
v_l_502_ = lean_ctor_get(v_l_5_, 3);
v_r_503_ = lean_ctor_get(v_l_5_, 4);
lean_inc(v_r_503_);
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_mul(v___x_504_, v_size_498_);
v___x_506_ = lean_nat_dec_lt(v___x_505_, v_size_499_);
lean_dec(v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_r_503_);
v___x_507_ = lean_nat_add(v___x_497_, v_size_499_);
v___x_508_ = lean_nat_add(v___x_507_, v_size_498_);
lean_dec(v___x_507_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_impl_496_);
lean_ctor_set(v___x_8_, 0, v___x_508_);
v___x_510_ = v___x_8_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_impl_496_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_577_; 
lean_inc(v_l_502_);
lean_inc(v_v_501_);
lean_inc(v_k_500_);
lean_inc(v_size_499_);
v_isSharedCheck_577_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_578_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_l_5_, 2);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_l_5_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_582_);
v___x_513_ = v_l_5_;
v_isShared_514_ = v_isSharedCheck_577_;
goto v_resetjp_512_;
}
else
{
lean_dec(v_l_5_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_577_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_size_515_; lean_object* v_size_516_; lean_object* v_k_517_; lean_object* v_v_518_; lean_object* v_l_519_; lean_object* v_r_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_size_515_ = lean_ctor_get(v_l_502_, 0);
v_size_516_ = lean_ctor_get(v_r_503_, 0);
v_k_517_ = lean_ctor_get(v_r_503_, 1);
v_v_518_ = lean_ctor_get(v_r_503_, 2);
v_l_519_ = lean_ctor_get(v_r_503_, 3);
v_r_520_ = lean_ctor_get(v_r_503_, 4);
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = lean_nat_mul(v___x_521_, v_size_515_);
v___x_523_ = lean_nat_dec_lt(v_size_516_, v___x_522_);
lean_dec(v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_552_; 
lean_inc(v_r_520_);
lean_inc(v_l_519_);
lean_inc(v_v_518_);
lean_inc(v_k_517_);
v_isSharedCheck_552_ = !lean_is_exclusive(v_r_503_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_553_ = lean_ctor_get(v_r_503_, 4);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_r_503_, 3);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_r_503_, 2);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_r_503_, 1);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_r_503_, 0);
lean_dec(v_unused_557_);
v___x_525_ = v_r_503_;
v_isShared_526_ = v_isSharedCheck_552_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_r_503_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_552_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___x_540_; lean_object* v___y_542_; 
v___x_527_ = lean_nat_add(v___x_497_, v_size_499_);
lean_dec(v_size_499_);
v___x_528_ = lean_nat_add(v___x_527_, v_size_498_);
lean_dec(v___x_527_);
v___x_540_ = lean_nat_add(v___x_497_, v_size_515_);
if (lean_obj_tag(v_l_519_) == 0)
{
lean_object* v_size_550_; 
v_size_550_ = lean_ctor_get(v_l_519_, 0);
lean_inc(v_size_550_);
v___y_542_ = v_size_550_;
goto v___jp_541_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___y_542_ = v___x_551_;
goto v___jp_541_;
}
v___jp_529_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_nat_add(v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec(v___y_531_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 4, v_impl_496_);
lean_ctor_set(v___x_525_, 3, v_r_520_);
lean_ctor_set(v___x_525_, 2, v_v_4_);
lean_ctor_set(v___x_525_, 1, v_k_3_);
lean_ctor_set(v___x_525_, 0, v___x_533_);
v___x_535_ = v___x_525_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_r_520_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_impl_496_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v___x_535_);
lean_ctor_set(v___x_513_, 3, v___y_530_);
lean_ctor_set(v___x_513_, 2, v_v_518_);
lean_ctor_set(v___x_513_, 1, v_k_517_);
lean_ctor_set(v___x_513_, 0, v___x_528_);
v___x_537_ = v___x_513_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_k_517_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_v_518_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v___y_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_nat_add(v___x_540_, v___y_542_);
lean_dec(v___y_542_);
lean_dec(v___x_540_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_l_519_);
lean_ctor_set(v___x_8_, 3, v_l_502_);
lean_ctor_set(v___x_8_, 2, v_v_501_);
lean_ctor_set(v___x_8_, 1, v_k_500_);
lean_ctor_set(v___x_8_, 0, v___x_543_);
v___x_545_ = v___x_8_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_l_502_);
lean_ctor_set(v_reuseFailAlloc_549_, 4, v_l_519_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = lean_nat_add(v___x_497_, v_size_498_);
if (lean_obj_tag(v_r_520_) == 0)
{
lean_object* v_size_547_; 
v_size_547_ = lean_ctor_get(v_r_520_, 0);
lean_inc(v_size_547_);
v___y_530_ = v___x_545_;
v___y_531_ = v___x_546_;
v___y_532_ = v_size_547_;
goto v___jp_529_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___y_530_ = v___x_545_;
v___y_531_ = v___x_546_;
v___y_532_ = v___x_548_;
goto v___jp_529_;
}
}
}
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
lean_del_object(v___x_8_);
v___x_558_ = lean_nat_add(v___x_497_, v_size_499_);
lean_dec(v_size_499_);
v___x_559_ = lean_nat_add(v___x_558_, v_size_498_);
lean_dec(v___x_558_);
v___x_560_ = lean_nat_add(v___x_497_, v_size_498_);
v___x_561_ = lean_nat_add(v___x_560_, v_size_516_);
lean_dec(v___x_560_);
lean_inc_ref(v_impl_496_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v_impl_496_);
lean_ctor_set(v___x_513_, 3, v_r_503_);
lean_ctor_set(v___x_513_, 2, v_v_4_);
lean_ctor_set(v___x_513_, 1, v_k_3_);
lean_ctor_set(v___x_513_, 0, v___x_561_);
v___x_563_ = v___x_513_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_r_503_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_impl_496_);
v___x_563_ = v_reuseFailAlloc_576_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_isSharedCheck_570_ = !lean_is_exclusive(v_impl_496_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_impl_496_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_impl_496_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_impl_496_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_impl_496_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_impl_496_, 0);
lean_dec(v_unused_575_);
v___x_565_ = v_impl_496_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_impl_496_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_563_);
lean_ctor_set(v___x_565_, 3, v_l_502_);
lean_ctor_set(v___x_565_, 2, v_v_501_);
lean_ctor_set(v___x_565_, 1, v_k_500_);
lean_ctor_set(v___x_565_, 0, v___x_559_);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_l_502_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v___x_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_size_583_ = lean_ctor_get(v_impl_496_, 0);
v___x_584_ = lean_nat_add(v___x_497_, v_size_583_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_impl_496_);
lean_ctor_set(v___x_8_, 0, v___x_584_);
v___x_586_ = v___x_8_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_impl_496_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
if (lean_obj_tag(v_l_5_) == 0)
{
lean_object* v_l_588_; 
v_l_588_ = lean_ctor_get(v_l_5_, 3);
if (lean_obj_tag(v_l_588_) == 0)
{
lean_object* v_r_589_; 
lean_inc_ref(v_l_588_);
v_r_589_ = lean_ctor_get(v_l_5_, 4);
lean_inc(v_r_589_);
if (lean_obj_tag(v_r_589_) == 0)
{
lean_object* v_size_590_; lean_object* v_k_591_; lean_object* v_v_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_605_; 
v_size_590_ = lean_ctor_get(v_l_5_, 0);
v_k_591_ = lean_ctor_get(v_l_5_, 1);
v_v_592_ = lean_ctor_get(v_l_5_, 2);
v_isSharedCheck_605_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; lean_object* v_unused_607_; 
v_unused_606_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_606_);
v_unused_607_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_607_);
v___x_594_ = v_l_5_;
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_v_592_);
lean_inc(v_k_591_);
lean_inc(v_size_590_);
lean_dec(v_l_5_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_605_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_size_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v_size_596_ = lean_ctor_get(v_r_589_, 0);
v___x_597_ = lean_nat_add(v___x_497_, v_size_590_);
lean_dec(v_size_590_);
v___x_598_ = lean_nat_add(v___x_497_, v_size_596_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_impl_496_);
lean_ctor_set(v___x_594_, 3, v_r_589_);
lean_ctor_set(v___x_594_, 2, v_v_4_);
lean_ctor_set(v___x_594_, 1, v_k_3_);
lean_ctor_set(v___x_594_, 0, v___x_598_);
v___x_600_ = v___x_594_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_r_589_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_impl_496_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v___x_600_);
lean_ctor_set(v___x_8_, 3, v_l_588_);
lean_ctor_set(v___x_8_, 2, v_v_592_);
lean_ctor_set(v___x_8_, 1, v_k_591_);
lean_ctor_set(v___x_8_, 0, v___x_597_);
v___x_602_ = v___x_8_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_k_591_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_v_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_l_588_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_k_608_; lean_object* v_v_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_620_; 
v_k_608_ = lean_ctor_get(v_l_5_, 1);
v_v_609_ = lean_ctor_get(v_l_5_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_621_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_623_);
v___x_611_ = v_l_5_;
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_v_609_);
lean_inc(v_k_608_);
lean_dec(v_l_5_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(3u);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 3, v_r_589_);
lean_ctor_set(v___x_611_, 2, v_v_4_);
lean_ctor_set(v___x_611_, 1, v_k_3_);
lean_ctor_set(v___x_611_, 0, v___x_497_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_r_589_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_r_589_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v___x_615_);
lean_ctor_set(v___x_8_, 3, v_l_588_);
lean_ctor_set(v___x_8_, 2, v_v_609_);
lean_ctor_set(v___x_8_, 1, v_k_608_);
lean_ctor_set(v___x_8_, 0, v___x_613_);
v___x_617_ = v___x_8_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_l_588_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_object* v_r_624_; 
v_r_624_ = lean_ctor_get(v_l_5_, 4);
lean_inc(v_r_624_);
if (lean_obj_tag(v_r_624_) == 0)
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_649_; 
lean_inc(v_l_588_);
v_k_625_ = lean_ctor_get(v_l_5_, 1);
v_v_626_ = lean_ctor_get(v_l_5_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_l_5_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_650_ = lean_ctor_get(v_l_5_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_l_5_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_l_5_, 0);
lean_dec(v_unused_652_);
v___x_628_ = v_l_5_;
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_v_626_);
lean_inc(v_k_625_);
lean_dec(v_l_5_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_645_; 
v_k_630_ = lean_ctor_get(v_r_624_, 1);
v_v_631_ = lean_ctor_get(v_r_624_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_r_624_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; 
v_unused_646_ = lean_ctor_get(v_r_624_, 4);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_624_, 3);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_r_624_, 0);
lean_dec(v_unused_648_);
v___x_633_ = v_r_624_;
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_v_631_);
lean_inc(v_k_630_);
lean_dec(v_r_624_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(3u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_588_);
lean_ctor_set(v___x_633_, 3, v_l_588_);
lean_ctor_set(v___x_633_, 2, v_v_626_);
lean_ctor_set(v___x_633_, 1, v_k_625_);
lean_ctor_set(v___x_633_, 0, v___x_497_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_k_625_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_v_626_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_l_588_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_l_588_);
v___x_637_ = v_reuseFailAlloc_644_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v_l_588_);
lean_ctor_set(v___x_628_, 2, v_v_4_);
lean_ctor_set(v___x_628_, 1, v_k_3_);
lean_ctor_set(v___x_628_, 0, v___x_497_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_l_588_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_l_588_);
v___x_639_ = v_reuseFailAlloc_643_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v___x_639_);
lean_ctor_set(v___x_8_, 3, v___x_637_);
lean_ctor_set(v___x_8_, 2, v_v_631_);
lean_ctor_set(v___x_8_, 1, v_k_630_);
lean_ctor_set(v___x_8_, 0, v___x_635_);
v___x_641_ = v___x_8_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_631_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(2u);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_r_624_);
lean_ctor_set(v___x_8_, 0, v___x_653_);
v___x_655_ = v___x_8_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_r_624_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v___x_658_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 4, v_l_5_);
lean_ctor_set(v___x_8_, 0, v___x_497_);
v___x_658_ = v___x_8_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_k_3_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_v_4_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_l_5_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_l_5_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
}
else
{
return v_t_2_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object* v_k_662_, lean_object* v_t_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_k_662_, v_t_663_);
lean_dec(v_k_662_);
return v_res_664_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(lean_object* v_name_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_668_; lean_object* v_remaining_669_; uint8_t v___x_670_; 
v___x_668_ = lean_st_ref_get(v_a_666_);
v_remaining_669_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_remaining_669_);
lean_dec(v___x_668_);
v___x_670_ = l_Lean_NameSet_contains(v_remaining_669_, v_name_665_);
lean_dec(v_remaining_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_name_665_);
v___x_671_ = lean_box(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v_env_674_; lean_object* v_remaining_675_; lean_object* v_pending_676_; lean_object* v_postponedConstructors_677_; lean_object* v_postponedRecursors_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_690_; 
v___x_673_ = lean_st_ref_take(v_a_666_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
v_remaining_675_ = lean_ctor_get(v___x_673_, 1);
v_pending_676_ = lean_ctor_get(v___x_673_, 2);
v_postponedConstructors_677_ = lean_ctor_get(v___x_673_, 3);
v_postponedRecursors_678_ = lean_ctor_get(v___x_673_, 4);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_690_ == 0)
{
v___x_680_ = v___x_673_;
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_postponedRecursors_678_);
lean_inc(v_postponedConstructors_677_);
lean_inc(v_pending_676_);
lean_inc(v_remaining_675_);
lean_inc(v_env_674_);
lean_dec(v___x_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_690_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_665_, v_remaining_675_);
v___x_683_ = l_Lean_NameSet_insert(v_pending_676_, v_name_665_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 2, v___x_683_);
lean_ctor_set(v___x_680_, 1, v___x_682_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_env_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_postponedConstructors_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_postponedRecursors_678_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_st_ref_put(v_a_666_, v___x_685_);
v___x_687_ = lean_box(v___x_670_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_665_ = stack[0].m_obj;
lean_object* v_a_666_ = stack[1].m_obj;
lean_object* v_res_691_;
v_res_691_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_665_, v_a_666_);
stack->m_obj
 = v_res_691_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg___boxed(lean_object* v_name_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_692_, v_a_693_);
lean_dec(v_a_693_);
return v_res_695_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(lean_object* v_name_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_696_, v_a_698_);
return v___x_700_;
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_696_ = stack[0].m_obj;
lean_object* v_a_697_ = stack[1].m_obj;
lean_object* v_a_698_ = stack[2].m_obj;
lean_object* v_res_701_;
v_res_701_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(v_name_696_, v_a_697_, v_a_698_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___boxed(lean_object* v_name_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(v_name_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0(lean_object* v_00_u03b2_707_, lean_object* v_k_708_, lean_object* v_t_709_, lean_object* v_h_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_k_708_, v_t_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___boxed(lean_object* v_00_u03b2_712_, lean_object* v_k_713_, lean_object* v_t_714_, lean_object* v_h_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0(v_00_u03b2_712_, v_k_713_, v_t_714_, v_h_715_);
lean_dec(v_k_713_);
return v_res_716_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(lean_object* v_ex_717_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = l_Lean_Options_empty;
v___x_720_ = l_Lean_Kernel_Exception_toMessageData(v_ex_717_, v___x_719_);
v___x_721_ = l_Lean_MessageData_toString(v___x_720_);
v___x_722_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_717_ = stack[0].m_obj;
lean_object* v_res_724_;
v_res_724_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_ex_717_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg___boxed(lean_object* v_ex_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_ex_725_);
return v_res_727_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(lean_object* v_ex_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_ex_728_);
return v___x_732_;
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_728_ = stack[0].m_obj;
lean_object* v_a_729_ = stack[1].m_obj;
lean_object* v_a_730_ = stack[2].m_obj;
lean_object* v_res_733_;
v_res_733_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(v_ex_728_, v_a_729_, v_a_730_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___boxed(lean_object* v_ex_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(v_ex_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_738_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(lean_object* v_d_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_env_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_742_ = lean_st_ref_get(v_a_740_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_742_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_box(0);
v___x_746_ = lean_add_decl(v_env_743_, v___x_744_, v___x_744_, v_d_739_, v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_a_747_);
return v___x_748_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_771_; 
v_a_749_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_771_ == 0)
{
v___x_751_ = v___x_746_;
v_isShared_752_ = v_isSharedCheck_771_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_771_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v_remaining_754_; lean_object* v_pending_755_; lean_object* v_postponedConstructors_756_; lean_object* v_postponedRecursors_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_769_; 
v___x_753_ = lean_st_ref_take(v_a_740_);
v_remaining_754_ = lean_ctor_get(v___x_753_, 1);
v_pending_755_ = lean_ctor_get(v___x_753_, 2);
v_postponedConstructors_756_ = lean_ctor_get(v___x_753_, 3);
v_postponedRecursors_757_ = lean_ctor_get(v___x_753_, 4);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_770_);
v___x_759_ = v___x_753_;
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_postponedRecursors_757_);
lean_inc(v_postponedConstructors_756_);
lean_inc(v_pending_755_);
lean_inc(v_remaining_754_);
lean_dec(v___x_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_769_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_box(0);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_a_749_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_749_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_remaining_754_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_pending_755_);
lean_ctor_set(v_reuseFailAlloc_768_, 3, v_postponedConstructors_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 4, v_postponedRecursors_757_);
v___x_763_ = v_reuseFailAlloc_768_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_st_ref_put(v_a_740_, v___x_763_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 0);
lean_ctor_set(v___x_751_, 0, v___x_761_);
v___x_766_ = v___x_751_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_739_ = stack[0].m_obj;
lean_object* v_a_740_ = stack[1].m_obj;
lean_object* v_res_772_;
v_res_772_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v_d_739_, v_a_740_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg___boxed(lean_object* v_d_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v_d_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec(v_d_773_);
return v_res_776_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(lean_object* v_d_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v_d_777_, v_a_779_);
return v___x_781_;
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_777_ = stack[0].m_obj;
lean_object* v_a_778_ = stack[1].m_obj;
lean_object* v_a_779_ = stack[2].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(v_d_777_, v_a_778_, v_a_779_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___boxed(lean_object* v_d_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(v_d_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_d_783_);
return v_res_787_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0(void){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_instMonadEIO___redArg();
return v___x_788_;
}
}
lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___x_27806__overap_798_; lean_object* v___x_799_; 
v___x_793_ = lean_obj_once(&l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0, &l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0_once, _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0);
v___x_794_ = l_StateRefT_x27_instMonad___redArg(v___x_793_);
v___x_795_ = lean_box(0);
v___x_796_ = l_instInhabitedOfMonad___redArg(v___x_794_, v___x_795_);
v___f_797_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_797_, 0, v___x_796_);
v___x_27806__overap_798_ = lean_panic_fn_borrowed(v___f_797_, v_msg_789_);
lean_dec_ref(v___f_797_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
v___x_799_ = lean_apply_3(v___x_27806__overap_798_, v___y_790_, v___y_791_, lean_box(0));
return v___x_799_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_789_ = stack[0].m_obj;
lean_object* v___y_790_ = stack[1].m_obj;
lean_object* v___y_791_ = stack[2].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v_msg_789_, v___y_790_, v___y_791_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___boxed(lean_object* v_msg_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v_msg_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_805_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(lean_object* v_name_808_, lean_object* v_____r_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_env_814_; lean_object* v_remaining_815_; lean_object* v_pending_816_; lean_object* v_postponedConstructors_817_; lean_object* v_postponedRecursors_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_829_; 
v___x_813_ = lean_st_ref_take(v___y_811_);
v_env_814_ = lean_ctor_get(v___x_813_, 0);
v_remaining_815_ = lean_ctor_get(v___x_813_, 1);
v_pending_816_ = lean_ctor_get(v___x_813_, 2);
v_postponedConstructors_817_ = lean_ctor_get(v___x_813_, 3);
v_postponedRecursors_818_ = lean_ctor_get(v___x_813_, 4);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_829_ == 0)
{
v___x_820_ = v___x_813_;
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_postponedRecursors_818_);
lean_inc(v_postponedConstructors_817_);
lean_inc(v_pending_816_);
lean_inc(v_remaining_815_);
lean_inc(v_env_814_);
lean_dec(v___x_813_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_829_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_808_, v_pending_816_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_env_814_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_remaining_815_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_postponedConstructors_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_postponedRecursors_818_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_st_ref_put(v___y_811_, v___x_824_);
v___x_826_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0));
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_808_ = stack[0].m_obj;
lean_object* v_____r_809_ = stack[1].m_obj;
lean_object* v___y_810_ = stack[2].m_obj;
lean_object* v___y_811_ = stack[3].m_obj;
lean_object* v_res_830_;
v_res_830_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_808_, v_____r_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed(lean_object* v_name_831_, lean_object* v_____r_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_831_, v_____r_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v_name_831_);
return v_res_836_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(lean_object* v_val_837_, lean_object* v___f_838_, lean_object* v_____r_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_843_, 0, v_val_837_);
v___x_844_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_843_, v___y_841_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
v___x_846_ = lean_apply_4(v___f_838_, v_a_845_, v___y_840_, v___y_841_, lean_box(0));
return v___x_846_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec_ref(v___f_838_);
v_a_847_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_844_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_844_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_837_ = stack[0].m_obj;
lean_object* v___f_838_ = stack[1].m_obj;
lean_object* v_____r_839_ = stack[2].m_obj;
lean_object* v___y_840_ = stack[3].m_obj;
lean_object* v___y_841_ = stack[4].m_obj;
lean_object* v_res_855_;
v_res_855_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_837_, v___f_838_, v_____r_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed(lean_object* v_val_856_, lean_object* v___f_857_, lean_object* v_____r_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_856_, v___f_857_, v_____r_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
return v_res_862_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(lean_object* v___f_863_, lean_object* v_x_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_box(0);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
v___x_869_ = lean_apply_4(v___f_863_, v___x_868_, v___y_865_, v___y_866_, lean_box(0));
return v___x_869_;
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_863_ = stack[0].m_obj;
lean_object* v_x_864_ = stack[1].m_obj;
lean_object* v___y_865_ = stack[2].m_obj;
lean_object* v___y_866_ = stack[3].m_obj;
lean_object* v_res_870_;
v_res_870_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_863_, v_x_864_, v___y_865_, v___y_866_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2___boxed(lean_object* v___f_871_, lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_871_, v_x_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v_x_872_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(lean_object* v_a_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_box(0);
return v___x_879_;
}
else
{
lean_object* v_key_880_; lean_object* v_value_881_; lean_object* v_tail_882_; uint8_t v___x_883_; 
v_key_880_ = lean_ctor_get(v_x_878_, 0);
v_value_881_ = lean_ctor_get(v_x_878_, 1);
v_tail_882_ = lean_ctor_get(v_x_878_, 2);
v___x_883_ = lean_name_eq(v_key_880_, v_a_877_);
if (v___x_883_ == 0)
{
v_x_878_ = v_tail_882_;
goto _start;
}
else
{
lean_object* v___x_885_; 
lean_inc(v_value_881_);
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_value_881_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec(v_a_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(lean_object* v_m_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_buckets_891_; lean_object* v___x_892_; uint64_t v___y_894_; 
v_buckets_891_ = lean_ctor_get(v_m_889_, 1);
v___x_892_ = lean_array_get_size(v_buckets_891_);
if (lean_obj_tag(v_a_890_) == 0)
{
uint64_t v___x_908_; 
v___x_908_ = 1723ULL;
v___y_894_ = v___x_908_;
goto v___jp_893_;
}
else
{
uint64_t v_hash_909_; 
v_hash_909_ = lean_ctor_get_uint64(v_a_890_, sizeof(void*)*2);
v___y_894_ = v_hash_909_;
goto v___jp_893_;
}
v___jp_893_:
{
uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v_fold_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_895_ = 32ULL;
v___x_896_ = lean_uint64_shift_right(v___y_894_, v___x_895_);
v_fold_897_ = lean_uint64_xor(v___y_894_, v___x_896_);
v___x_898_ = 16ULL;
v___x_899_ = lean_uint64_shift_right(v_fold_897_, v___x_898_);
v___x_900_ = lean_uint64_xor(v_fold_897_, v___x_899_);
v___x_901_ = lean_uint64_to_usize(v___x_900_);
v___x_902_ = lean_usize_of_nat(v___x_892_);
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_sub(v___x_902_, v___x_903_);
v___x_905_ = lean_usize_land(v___x_901_, v___x_904_);
v___x_906_ = lean_array_uget_borrowed(v_buckets_891_, v___x_905_);
v___x_907_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_890_, v___x_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg___boxed(lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_m_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_m_910_);
return v_res_912_;
}
}
uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
if (lean_obj_tag(v_x_913_) == 0)
{
if (lean_obj_tag(v_x_914_) == 0)
{
uint8_t v___x_915_; 
v___x_915_ = 1;
return v___x_915_;
}
else
{
uint8_t v___x_916_; 
v___x_916_ = 0;
return v___x_916_;
}
}
else
{
if (lean_obj_tag(v_x_914_) == 0)
{
uint8_t v___x_917_; 
v___x_917_ = 0;
return v___x_917_;
}
else
{
lean_object* v_head_918_; lean_object* v_tail_919_; lean_object* v_head_920_; lean_object* v_tail_921_; uint8_t v___x_922_; 
v_head_918_ = lean_ctor_get(v_x_913_, 0);
v_tail_919_ = lean_ctor_get(v_x_913_, 1);
v_head_920_ = lean_ctor_get(v_x_914_, 0);
v_tail_921_ = lean_ctor_get(v_x_914_, 1);
v___x_922_ = lean_name_eq(v_head_918_, v_head_920_);
if (v___x_922_ == 0)
{
return v___x_922_;
}
else
{
v_x_913_ = v_tail_919_;
v_x_914_ = v_tail_921_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_913_ = stack[0].m_obj;
lean_object* v_x_914_ = stack[1].m_obj;
uint8_t v_res_924_;
v_res_924_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_x_913_, v_x_914_);
stack->m_num = v_res_924_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4___boxed(lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_x_925_, v_x_926_);
lean_dec(v_x_926_);
lean_dec(v_x_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(lean_object* v_as_x27_929_, lean_object* v_b_930_, lean_object* v___y_931_){
_start:
{
if (lean_obj_tag(v_as_x27_929_) == 0)
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_b_930_);
return v___x_933_;
}
else
{
lean_object* v_head_934_; lean_object* v_tail_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_env_938_; lean_object* v_remaining_939_; lean_object* v_pending_940_; lean_object* v_postponedConstructors_941_; lean_object* v_postponedRecursors_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_954_; 
v_head_934_ = lean_ctor_get(v_as_x27_929_, 0);
v_tail_935_ = lean_ctor_get(v_as_x27_929_, 1);
v___x_936_ = lean_box(0);
v___x_937_ = lean_st_ref_take(v___y_931_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
v_remaining_939_ = lean_ctor_get(v___x_937_, 1);
v_pending_940_ = lean_ctor_get(v___x_937_, 2);
v_postponedConstructors_941_ = lean_ctor_get(v___x_937_, 3);
v_postponedRecursors_942_ = lean_ctor_get(v___x_937_, 4);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_954_ == 0)
{
v___x_944_ = v___x_937_;
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_postponedRecursors_942_);
lean_inc(v_postponedConstructors_941_);
lean_inc(v_pending_940_);
lean_inc(v_remaining_939_);
lean_inc(v_env_938_);
lean_dec(v___x_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_946_ = l_Lean_ConstantInfo_name(v_head_934_);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v___x_946_, v_remaining_939_);
v___x_948_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v___x_946_, v_pending_940_);
lean_dec(v___x_946_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v___x_948_);
lean_ctor_set(v___x_944_, 1, v___x_947_);
v___x_950_ = v___x_944_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_env_938_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_postponedConstructors_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_postponedRecursors_942_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_st_ref_put(v___y_931_, v___x_950_);
v_as_x27_929_ = v_tail_935_;
v_b_930_ = v___x_936_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_929_ = stack[0].m_obj;
lean_object* v_b_930_ = stack[1].m_obj;
lean_object* v___y_931_ = stack[2].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_929_, v_b_930_, v___y_931_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg___boxed(lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_956_, v_b_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec(v_as_x27_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1_spec__4(lean_object* v_msg_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Lean_instInhabitedConstantInfo_default;
v___x_963_ = lean_panic_fn_borrowed(v___x_962_, v_msg_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_967_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__2));
v___x_968_ = lean_unsigned_to_nat(11u);
v___x_969_ = lean_unsigned_to_nat(163u);
v___x_970_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__1));
v___x_971_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__0));
v___x_972_ = l_mkPanicMessageWithDecl(v___x_971_, v___x_970_, v___x_969_, v___x_968_, v___x_967_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(lean_object* v_a_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___closed__3);
v___x_976_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1_spec__4(v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_key_977_; lean_object* v_value_978_; lean_object* v_tail_979_; uint8_t v___x_980_; 
v_key_977_ = lean_ctor_get(v_x_974_, 0);
v_value_978_ = lean_ctor_get(v_x_974_, 1);
v_tail_979_ = lean_ctor_get(v_x_974_, 2);
v___x_980_ = lean_name_eq(v_key_977_, v_a_973_);
if (v___x_980_ == 0)
{
v_x_974_ = v_tail_979_;
goto _start;
}
else
{
lean_inc(v_value_978_);
return v_value_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(v_a_982_, v_x_983_);
lean_dec(v_x_983_);
lean_dec(v_a_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object* v_m_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_buckets_987_; lean_object* v___x_988_; uint64_t v___y_990_; 
v_buckets_987_ = lean_ctor_get(v_m_985_, 1);
v___x_988_ = lean_array_get_size(v_buckets_987_);
if (lean_obj_tag(v_a_986_) == 0)
{
uint64_t v___x_1004_; 
v___x_1004_ = 1723ULL;
v___y_990_ = v___x_1004_;
goto v___jp_989_;
}
else
{
uint64_t v_hash_1005_; 
v_hash_1005_ = lean_ctor_get_uint64(v_a_986_, sizeof(void*)*2);
v___y_990_ = v_hash_1005_;
goto v___jp_989_;
}
v___jp_989_:
{
uint64_t v___x_991_; uint64_t v___x_992_; uint64_t v_fold_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_991_ = 32ULL;
v___x_992_ = lean_uint64_shift_right(v___y_990_, v___x_991_);
v_fold_993_ = lean_uint64_xor(v___y_990_, v___x_992_);
v___x_994_ = 16ULL;
v___x_995_ = lean_uint64_shift_right(v_fold_993_, v___x_994_);
v___x_996_ = lean_uint64_xor(v_fold_993_, v___x_995_);
v___x_997_ = lean_uint64_to_usize(v___x_996_);
v___x_998_ = lean_usize_of_nat(v___x_988_);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_sub(v___x_998_, v___x_999_);
v___x_1001_ = lean_usize_land(v___x_997_, v___x_1000_);
v___x_1002_ = lean_array_uget_borrowed(v_buckets_987_, v___x_1001_);
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(v_a_986_, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___boxed(lean_object* v_m_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(v_m_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_m_1006_);
return v_res_1008_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = l_List_reverse___redArg(v_x_1010_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
else
{
lean_object* v_head_1015_; lean_object* v_tail_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1025_; 
v_head_1015_ = lean_ctor_get(v_x_1009_, 0);
v_tail_1016_ = lean_ctor_get(v_x_1009_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1018_ = v_x_1009_;
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_tail_1016_);
lean_inc(v_head_1015_);
lean_dec(v_x_1009_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1025_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(v___y_1011_, v_head_1015_);
lean_dec(v_head_1015_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_x_1010_);
lean_ctor_set(v___x_1018_, 0, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_x_1010_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v_x_1009_ = v_tail_1016_;
v_x_1010_ = v___x_1022_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1009_ = stack[0].m_obj;
lean_object* v_x_1010_ = stack[1].m_obj;
lean_object* v___y_1011_ = stack[2].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_x_1009_, v_x_1010_, v___y_1011_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_x_1027_, v_x_1028_, v___y_1029_);
lean_dec_ref(v___y_1029_);
return v_res_1031_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = l_List_reverse___redArg(v_x_1033_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v_head_1039_; lean_object* v_tail_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1054_; 
v_head_1039_ = lean_ctor_get(v_x_1032_, 0);
v_tail_1040_ = lean_ctor_get(v_x_1032_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1032_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1042_ = v_x_1032_;
v_isShared_1043_ = v_isSharedCheck_1054_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_tail_1040_);
lean_inc(v_head_1039_);
lean_dec(v_x_1032_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1054_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v_ctors_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1044_ = l_Lean_ConstantInfo_inductiveVal_x21(v_head_1039_);
v_ctors_1045_ = lean_ctor_get(v___x_1044_, 4);
lean_inc(v_ctors_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_box(0);
v___x_1047_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_ctors_1045_, v___x_1046_, v___y_1034_);
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_head_1039_);
lean_ctor_set(v___x_1049_, 1, v_a_1048_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v_x_1033_);
lean_ctor_set(v___x_1042_, 0, v___x_1049_);
v___x_1051_ = v___x_1042_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_x_1033_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v_x_1032_ = v_tail_1040_;
v_x_1033_ = v___x_1051_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1032_ = stack[0].m_obj;
lean_object* v_x_1033_ = stack[1].m_obj;
lean_object* v___y_1034_ = stack[2].m_obj;
lean_object* v___y_1035_ = stack[3].m_obj;
lean_object* v_res_1055_;
v_res_1055_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_x_1032_, v_x_1033_, v___y_1034_, v___y_1035_);
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_x_1056_, v_x_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
if (lean_obj_tag(v_a_1062_) == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = l_List_reverse___redArg(v_a_1063_);
return v___x_1064_;
}
else
{
lean_object* v_head_1065_; lean_object* v_tail_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
v_head_1065_ = lean_ctor_get(v_a_1062_, 0);
v_tail_1066_ = lean_ctor_get(v_a_1062_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_1062_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1068_ = v_a_1062_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_tail_1066_);
lean_inc(v_head_1065_);
lean_dec(v_a_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1070_ = l_Lean_ConstantInfo_name(v_head_1065_);
v___x_1071_ = l_Lean_ConstantInfo_type(v_head_1065_);
lean_dec(v_head_1065_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v_a_1063_);
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1074_ = v___x_1068_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_a_1063_);
v___x_1074_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
v_a_1062_ = v_tail_1066_;
v_a_1063_ = v___x_1074_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
if (lean_obj_tag(v_a_1078_) == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = l_List_reverse___redArg(v_a_1079_);
return v___x_1080_;
}
else
{
lean_object* v_head_1081_; lean_object* v_tail_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1097_; 
v_head_1081_ = lean_ctor_get(v_a_1078_, 0);
v_tail_1082_ = lean_ctor_get(v_a_1078_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1078_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1084_ = v_a_1078_;
v_isShared_1085_ = v_isSharedCheck_1097_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_tail_1082_);
lean_inc(v_head_1081_);
lean_dec(v_a_1078_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1097_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_fst_1086_ = lean_ctor_get(v_head_1081_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v_head_1081_, 1);
lean_inc(v_snd_1087_);
lean_dec(v_head_1081_);
v___x_1088_ = l_Lean_ConstantInfo_name(v_fst_1086_);
v___x_1089_ = l_Lean_ConstantInfo_type(v_fst_1086_);
lean_dec(v_fst_1086_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(v_snd_1087_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1088_);
lean_ctor_set(v___x_1092_, 1, v___x_1089_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v_a_1079_);
lean_ctor_set(v___x_1084_, 0, v___x_1092_);
v___x_1094_ = v___x_1084_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_a_1079_);
v___x_1094_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v_a_1078_ = v_tail_1082_;
v_a_1079_ = v___x_1094_;
goto _start;
}
}
}
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(lean_object* v_as_x27_1103_, lean_object* v_b_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
if (lean_obj_tag(v_as_x27_1103_) == 0)
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_b_1104_);
return v___x_1108_;
}
else
{
lean_object* v_head_1109_; lean_object* v_tail_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_head_1109_ = lean_ctor_get(v_as_x27_1103_, 0);
v_tail_1110_ = lean_ctor_get(v_as_x27_1103_, 1);
v___x_1111_ = lean_box(0);
lean_inc(v_head_1109_);
v___x_1112_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_1109_);
v___x_1113_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1112_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v_as_x27_1103_ = v_tail_1110_;
v_b_1104_ = v___x_1111_;
goto _start;
}
else
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1103_ = stack[0].m_obj;
lean_object* v_b_1104_ = stack[1].m_obj;
lean_object* v___y_1105_ = stack[2].m_obj;
lean_object* v___y_1106_ = stack[3].m_obj;
lean_object* v_res_1115_;
v_res_1115_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_1103_, v_b_1104_, v___y_1105_, v___y_1106_);
stack->m_obj
 = v_res_1115_;
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(lean_object* v_as_x27_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
if (lean_obj_tag(v_as_x27_1116_) == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_b_1117_);
return v___x_1121_;
}
else
{
lean_object* v_head_1122_; lean_object* v_tail_1123_; lean_object* v_snd_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_head_1122_ = lean_ctor_get(v_as_x27_1116_, 0);
v_tail_1123_ = lean_ctor_get(v_as_x27_1116_, 1);
v_snd_1124_ = lean_ctor_get(v_head_1122_, 1);
v___x_1125_ = lean_box(0);
v___x_1126_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_snd_1124_, v___x_1125_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_dec_ref_known(v___x_1126_, 1);
v_as_x27_1116_ = v_tail_1123_;
v_b_1117_ = v___x_1125_;
goto _start;
}
else
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1116_ = stack[0].m_obj;
lean_object* v_b_1117_ = stack[1].m_obj;
lean_object* v___y_1118_ = stack[2].m_obj;
lean_object* v___y_1119_ = stack[3].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1116_, v_b_1117_, v___y_1118_, v___y_1119_);
stack->m_obj
 = v_res_1128_;
}
static lean_object* _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6));
v___x_1133_ = lean_unsigned_to_nat(50u);
v___x_1134_ = lean_unsigned_to_nat(76u);
v___x_1135_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5));
v___x_1136_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4));
v___x_1137_ = l_mkPanicMessageWithDecl(v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_, v___x_1132_);
return v___x_1137_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(lean_object* v_name_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; 
lean_inc_n(v_name_1138_, 2);
v___f_1142_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1142_, 0, v_name_1138_);
v___x_1143_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_1138_, v_a_1140_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1343_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1343_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1343_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
v___x_1149_ = lean_box(0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_a_1139_, v_name_1138_);
if (lean_obj_tag(v___x_1153_) == 1)
{
lean_object* v_val_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1340_; 
v_val_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1340_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_val_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1340_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_inc(v_val_1154_);
v___x_1158_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_1154_);
v___x_1159_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1158_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1338_; 
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1339_);
v___x_1161_ = v___x_1159_;
v_isShared_1162_ = v_isSharedCheck_1338_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v___x_1159_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1338_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v_pending_1164_; uint8_t v___x_1165_; lean_object* v_a_1167_; lean_object* v___y_1182_; 
v___x_1163_ = lean_st_ref_get(v_a_1140_);
v_pending_1164_ = lean_ctor_get(v___x_1163_, 2);
lean_inc(v_pending_1164_);
lean_dec(v___x_1163_);
v___x_1165_ = l_Lean_NameSet_contains(v_pending_1164_, v_name_1138_);
lean_dec(v_pending_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_del_object(v___x_1161_);
lean_del_object(v___x_1156_);
lean_dec(v_val_1154_);
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
v___x_1193_ = lean_box(0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1193_);
v___x_1195_ = v___x_1146_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
switch(lean_obj_tag(v_val_1154_))
{
case 0:
{
lean_object* v_val_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1197_ = lean_ctor_get(v_val_1154_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_val_1154_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1199_ = v_val_1154_;
v_isShared_1200_ = v_isSharedCheck_1208_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_val_1197_);
lean_dec(v_val_1154_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1208_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_val_1197_);
v___x_1202_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1202_, v_a_1140_);
lean_dec_ref(v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1205_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v_a_1204_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1205_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1203_, 1);
v_a_1167_ = v_a_1206_;
goto v___jp_1166_;
}
}
}
}
case 1:
{
lean_object* v_val_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1209_ = lean_ctor_get(v_val_1154_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_val_1154_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1211_ = v_val_1154_;
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_val_1209_);
lean_dec(v_val_1154_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1220_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_val_1209_);
v___x_1214_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1214_, v_a_1140_);
lean_dec_ref(v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v_a_1216_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1217_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1215_, 1);
v_a_1167_ = v_a_1218_;
goto v___jp_1166_;
}
}
}
}
case 2:
{
lean_object* v_val_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v_env_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_val_1221_ = lean_ctor_get(v_val_1154_, 0);
lean_inc_ref_n(v_val_1221_, 2);
lean_inc_ref(v___f_1142_);
v___f_1222_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(v___f_1222_, 0, v_val_1221_);
lean_closure_set(v___f_1222_, 1, v___f_1142_);
v___x_1223_ = lean_st_ref_get(v_a_1140_);
v_env_1227_ = lean_ctor_get(v___x_1223_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1223_);
v___x_1228_ = l_Lean_ConstantInfo_name(v_val_1154_);
lean_dec_ref_known(v_val_1154_, 1);
v___x_1229_ = lean_environment_find(v_env_1227_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
if (lean_obj_tag(v_val_1230_) == 2)
{
lean_object* v_toConstantVal_1231_; lean_object* v_val_1232_; lean_object* v_toConstantVal_1233_; lean_object* v_all_1234_; lean_object* v_name_1235_; lean_object* v_levelParams_1236_; lean_object* v_type_1237_; lean_object* v_all_1238_; lean_object* v_name_1239_; lean_object* v_levelParams_1240_; lean_object* v_type_1241_; uint8_t v___y_1243_; uint8_t v___x_1250_; 
lean_inc_ref(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
lean_dec_ref(v___f_1222_);
v_toConstantVal_1231_ = lean_ctor_get(v_val_1221_, 0);
v_val_1232_ = lean_ctor_get(v_val_1230_, 0);
lean_inc_ref(v_val_1232_);
lean_dec_ref_known(v_val_1230_, 1);
v_toConstantVal_1233_ = lean_ctor_get(v_val_1232_, 0);
lean_inc_ref(v_toConstantVal_1233_);
v_all_1234_ = lean_ctor_get(v_val_1221_, 2);
v_name_1235_ = lean_ctor_get(v_toConstantVal_1231_, 0);
v_levelParams_1236_ = lean_ctor_get(v_toConstantVal_1231_, 1);
v_type_1237_ = lean_ctor_get(v_toConstantVal_1231_, 2);
v_all_1238_ = lean_ctor_get(v_val_1232_, 2);
lean_inc(v_all_1238_);
lean_dec_ref(v_val_1232_);
v_name_1239_ = lean_ctor_get(v_toConstantVal_1233_, 0);
lean_inc(v_name_1239_);
v_levelParams_1240_ = lean_ctor_get(v_toConstantVal_1233_, 1);
lean_inc(v_levelParams_1240_);
v_type_1241_ = lean_ctor_get(v_toConstantVal_1233_, 2);
lean_inc_ref(v_type_1241_);
lean_dec_ref(v_toConstantVal_1233_);
v___x_1250_ = lean_name_eq(v_name_1235_, v_name_1239_);
lean_dec(v_name_1239_);
if (v___x_1250_ == 0)
{
lean_dec_ref(v_type_1241_);
v___y_1243_ = v___x_1250_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_expr_eqv(v_type_1237_, v_type_1241_);
lean_dec_ref(v_type_1241_);
v___y_1243_ = v___x_1251_;
goto v___jp_1242_;
}
v___jp_1242_:
{
if (v___y_1243_ == 0)
{
lean_dec(v_levelParams_1240_);
lean_dec(v_all_1238_);
lean_del_object(v___x_1146_);
goto v___jp_1224_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_levelParams_1236_, v_levelParams_1240_);
lean_dec(v_levelParams_1240_);
if (v___x_1244_ == 0)
{
lean_dec(v_all_1238_);
lean_del_object(v___x_1146_);
goto v___jp_1224_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_all_1234_, v_all_1238_);
lean_dec(v_all_1238_);
if (v___x_1245_ == 0)
{
lean_del_object(v___x_1146_);
goto v___jp_1224_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec_ref(v_val_1221_);
lean_del_object(v___x_1161_);
lean_del_object(v___x_1156_);
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
v___x_1246_ = lean_box(0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1246_);
v___x_1248_ = v___x_1146_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
else
{
lean_object* v___x_1252_; 
lean_dec_ref(v_val_1221_);
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v___x_1252_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1222_, v___x_1229_, v_a_1139_, v_a_1140_);
lean_dec_ref_known(v___x_1229_, 1);
v___y_1182_ = v___x_1252_;
goto v___jp_1181_;
}
}
else
{
lean_object* v___x_1253_; 
lean_dec_ref(v_val_1221_);
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v___x_1253_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1222_, v___x_1229_, v_a_1139_, v_a_1140_);
lean_dec(v___x_1229_);
v___y_1182_ = v___x_1253_;
goto v___jp_1181_;
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_1221_, v___f_1142_, v___x_1225_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1226_;
goto v___jp_1181_;
}
}
case 3:
{
lean_object* v_val_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1265_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1254_ = lean_ctor_get(v_val_1154_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_val_1154_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1256_ = v_val_1154_;
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_val_1254_);
lean_dec(v_val_1154_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1265_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_val_1254_);
v___x_1259_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1259_, v_a_1140_);
lean_dec_ref(v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v_a_1261_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1262_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1260_, 1);
v_a_1167_ = v_a_1263_;
goto v___jp_1166_;
}
}
}
}
case 4:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v_val_1154_, 1);
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3));
v___x_1267_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v___x_1266_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref_known(v___x_1267_, 1);
v___x_1268_ = lean_box(4);
v___x_1269_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1268_, v_a_1140_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v_a_1270_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1271_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1269_, 1);
v_a_1167_ = v_a_1272_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1273_; 
v_a_1273_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1267_, 1);
v_a_1167_ = v_a_1273_;
goto v___jp_1166_;
}
}
case 5:
{
lean_object* v_val_1274_; lean_object* v_toConstantVal_1275_; lean_object* v_numParams_1276_; lean_object* v_all_1277_; lean_object* v_levelParams_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1274_ = lean_ctor_get(v_val_1154_, 0);
lean_inc_ref(v_val_1274_);
lean_dec_ref_known(v_val_1154_, 1);
v_toConstantVal_1275_ = lean_ctor_get(v_val_1274_, 0);
lean_inc_ref(v_toConstantVal_1275_);
v_numParams_1276_ = lean_ctor_get(v_val_1274_, 1);
lean_inc(v_numParams_1276_);
v_all_1277_ = lean_ctor_get(v_val_1274_, 3);
lean_inc(v_all_1277_);
lean_dec_ref(v_val_1274_);
v_levelParams_1278_ = lean_ctor_get(v_toConstantVal_1275_, 1);
lean_inc(v_levelParams_1278_);
lean_dec_ref(v_toConstantVal_1275_);
v___x_1279_ = lean_box(0);
v___x_1280_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_all_1277_, v___x_1279_, v_a_1139_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_box(0);
v___x_1283_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_a_1281_, v___x_1282_, v_a_1140_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1283_, 1);
v___x_1284_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_a_1281_, v___x_1279_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_a_1285_, v___x_1282_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref_known(v___x_1286_, 1);
v___x_1287_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(v_a_1285_, v___x_1279_);
v___x_1288_ = 0;
v___x_1289_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1289_, 0, v_levelParams_1278_);
lean_ctor_set(v___x_1289_, 1, v_numParams_1276_);
lean_ctor_set(v___x_1289_, 2, v___x_1287_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*3, v___x_1288_);
v___x_1290_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1289_, v_a_1140_);
lean_dec_ref_known(v___x_1289_, 3);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v_a_1291_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1292_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1293_; 
v_a_1293_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1290_, 1);
v_a_1167_ = v_a_1293_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1294_; 
lean_dec(v_a_1285_);
lean_dec(v_levelParams_1278_);
lean_dec(v_numParams_1276_);
v_a_1294_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1286_, 1);
v_a_1167_ = v_a_1294_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1295_; 
lean_dec(v_levelParams_1278_);
lean_dec(v_numParams_1276_);
v_a_1295_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1284_, 1);
v_a_1167_ = v_a_1295_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1296_; 
lean_dec(v_a_1281_);
lean_dec(v_levelParams_1278_);
lean_dec(v_numParams_1276_);
v_a_1296_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1283_, 1);
v_a_1167_ = v_a_1296_;
goto v___jp_1166_;
}
}
else
{
lean_object* v_a_1297_; 
lean_dec(v_levelParams_1278_);
lean_dec(v_numParams_1276_);
v_a_1297_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1280_, 1);
v_a_1167_ = v_a_1297_;
goto v___jp_1166_;
}
}
case 6:
{
lean_object* v_val_1298_; lean_object* v___x_1299_; lean_object* v_toConstantVal_1300_; lean_object* v_env_1301_; lean_object* v_remaining_1302_; lean_object* v_pending_1303_; lean_object* v_postponedConstructors_1304_; lean_object* v_postponedRecursors_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1298_ = lean_ctor_get(v_val_1154_, 0);
lean_inc_ref(v_val_1298_);
lean_dec_ref_known(v_val_1154_, 1);
v___x_1299_ = lean_st_ref_take(v_a_1140_);
v_toConstantVal_1300_ = lean_ctor_get(v_val_1298_, 0);
lean_inc_ref(v_toConstantVal_1300_);
lean_dec_ref(v_val_1298_);
v_env_1301_ = lean_ctor_get(v___x_1299_, 0);
v_remaining_1302_ = lean_ctor_get(v___x_1299_, 1);
v_pending_1303_ = lean_ctor_get(v___x_1299_, 2);
v_postponedConstructors_1304_ = lean_ctor_get(v___x_1299_, 3);
v_postponedRecursors_1305_ = lean_ctor_get(v___x_1299_, 4);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1307_ = v___x_1299_;
v_isShared_1308_ = v_isSharedCheck_1317_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_postponedRecursors_1305_);
lean_inc(v_postponedConstructors_1304_);
lean_inc(v_pending_1303_);
lean_inc(v_remaining_1302_);
lean_inc(v_env_1301_);
lean_dec(v___x_1299_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1317_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_name_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v_name_1309_ = lean_ctor_get(v_toConstantVal_1300_, 0);
lean_inc(v_name_1309_);
lean_dec_ref(v_toConstantVal_1300_);
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Lean_NameSet_insert(v_postponedConstructors_1304_, v_name_1309_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 3, v___x_1311_);
v___x_1313_ = v___x_1307_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_env_1301_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_remaining_1302_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_pending_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_postponedRecursors_1305_);
v___x_1313_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_st_ref_put(v_a_1140_, v___x_1313_);
v___x_1315_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v___x_1310_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1315_;
goto v___jp_1181_;
}
}
}
default: 
{
lean_object* v_val_1318_; lean_object* v___x_1319_; lean_object* v_toConstantVal_1320_; lean_object* v_env_1321_; lean_object* v_remaining_1322_; lean_object* v_pending_1323_; lean_object* v_postponedConstructors_1324_; lean_object* v_postponedRecursors_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1337_; 
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
v_val_1318_ = lean_ctor_get(v_val_1154_, 0);
lean_inc_ref(v_val_1318_);
lean_dec_ref_known(v_val_1154_, 1);
v___x_1319_ = lean_st_ref_take(v_a_1140_);
v_toConstantVal_1320_ = lean_ctor_get(v_val_1318_, 0);
lean_inc_ref(v_toConstantVal_1320_);
lean_dec_ref(v_val_1318_);
v_env_1321_ = lean_ctor_get(v___x_1319_, 0);
v_remaining_1322_ = lean_ctor_get(v___x_1319_, 1);
v_pending_1323_ = lean_ctor_get(v___x_1319_, 2);
v_postponedConstructors_1324_ = lean_ctor_get(v___x_1319_, 3);
v_postponedRecursors_1325_ = lean_ctor_get(v___x_1319_, 4);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1327_ = v___x_1319_;
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_postponedRecursors_1325_);
lean_inc(v_postponedConstructors_1324_);
lean_inc(v_pending_1323_);
lean_inc(v_remaining_1322_);
lean_inc(v_env_1321_);
lean_dec(v___x_1319_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v_name_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_name_1329_ = lean_ctor_get(v_toConstantVal_1320_, 0);
lean_inc(v_name_1329_);
lean_dec_ref(v_toConstantVal_1320_);
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Lean_NameSet_insert(v_postponedRecursors_1325_, v_name_1329_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 4, v___x_1331_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_env_1321_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_remaining_1322_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_pending_1323_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_postponedConstructors_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_st_ref_put(v_a_1140_, v___x_1333_);
v___x_1335_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1138_, v___x_1330_, v_a_1139_, v_a_1140_);
v___y_1182_ = v___x_1335_;
goto v___jp_1181_;
}
}
}
}
}
v___jp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0));
v___x_1169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1138_, v___x_1165_);
v___x_1170_ = lean_string_append(v___x_1168_, v___x_1169_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1));
v___x_1172_ = lean_string_append(v___x_1170_, v___x_1171_);
v___x_1173_ = lean_io_error_to_string(v_a_1167_);
v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
lean_dec_ref(v___x_1173_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 18);
lean_ctor_set(v___x_1156_, 0, v___x_1174_);
v___x_1176_ = v___x_1156_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 1);
lean_ctor_set(v___x_1161_, 0, v___x_1176_);
v___x_1178_ = v___x_1161_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
v___jp_1181_:
{
if (lean_obj_tag(v___y_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
lean_del_object(v___x_1161_);
lean_del_object(v___x_1156_);
lean_dec(v_name_1138_);
v_a_1183_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___y_1182_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___y_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_a_1187_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_a_1187_);
lean_dec(v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_a_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; 
v_a_1192_ = lean_ctor_get(v___y_1182_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___y_1182_, 1);
v_a_1167_ = v_a_1192_;
goto v___jp_1166_;
}
}
}
}
else
{
lean_del_object(v___x_1156_);
lean_dec(v_val_1154_);
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
return v___x_1159_;
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v___x_1153_);
lean_del_object(v___x_1146_);
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7, &l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7_once, _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7);
v___x_1342_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v___x_1341_, v_a_1139_, v_a_1140_);
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___f_1142_);
lean_dec(v_name_1138_);
v_a_1344_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1143_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1143_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1138_ = stack[0].m_obj;
lean_object* v_a_1139_ = stack[1].m_obj;
lean_object* v_a_1140_ = stack[2].m_obj;
lean_object* v_res_1352_;
v_res_1352_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_name_1138_, v_a_1139_, v_a_1140_);
stack->m_obj
 = v_res_1352_;
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(lean_object* v_init_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 0)
{
lean_object* v_k_1358_; lean_object* v_l_1359_; lean_object* v_r_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_k_1358_ = lean_ctor_get(v_x_1354_, 1);
lean_inc(v_k_1358_);
v_l_1359_ = lean_ctor_get(v_x_1354_, 3);
lean_inc(v_l_1359_);
v_r_1360_ = lean_ctor_get(v_x_1354_, 4);
lean_inc(v_r_1360_);
lean_dec_ref_known(v_x_1354_, 5);
v___x_1361_ = lean_box(0);
v___x_1362_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v_init_1353_, v_l_1359_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref_known(v___x_1362_, 1);
v___x_1363_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_k_1358_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_dec_ref_known(v___x_1363_, 1);
v_init_1353_ = v___x_1361_;
v_x_1354_ = v_r_1360_;
goto _start;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_r_1360_);
v_a_1365_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1363_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_dec(v_r_1360_);
lean_dec(v_k_1358_);
return v___x_1362_;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_init_1353_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1353_ = stack[0].m_obj;
lean_object* v_x_1354_ = stack[1].m_obj;
lean_object* v___y_1355_ = stack[2].m_obj;
lean_object* v___y_1356_ = stack[3].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v_init_1353_, v_x_1354_, v___y_1355_, v___y_1356_);
stack->m_obj
 = v_res_1375_;
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(lean_object* v_names_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v___x_1380_, v_names_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1389_);
v___x_1383_ = v___x_1381_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v___x_1381_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1380_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_a_1390_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1381_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1381_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_1376_ = stack[0].m_obj;
lean_object* v_a_1377_ = stack[1].m_obj;
lean_object* v_a_1378_ = stack[2].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v_names_1376_, v_a_1377_, v_a_1378_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants___boxed(lean_object* v_names_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v_names_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object* v_as_x27_1404_, lean_object* v_b_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_1404_, v_b_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v_as_x27_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg___boxed(lean_object* v_as_x27_1410_, lean_object* v_b_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1410_, v_b_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v_as_x27_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12___boxed(lean_object* v_init_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v_init_1416_, v_x_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___boxed(lean_object* v_name_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_name_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
return v_res_1426_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_x_1427_, v_x_1428_, v___y_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1427_ = stack[0].m_obj;
lean_object* v_x_1428_ = stack[1].m_obj;
lean_object* v___y_1429_ = stack[2].m_obj;
lean_object* v___y_1430_ = stack[3].m_obj;
lean_object* v_res_1433_;
v_res_1433_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(v_x_1427_, v_x_1428_, v___y_1429_, v___y_1430_);
stack->m_obj
 = v_res_1433_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___boxed(lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(v_x_1434_, v_x_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(lean_object* v_00_u03b2_1440_, lean_object* v_m_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_m_1441_, v_a_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_m_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(v_00_u03b2_1444_, v_m_1445_, v_a_1446_);
lean_dec(v_a_1446_);
lean_dec_ref(v_m_1445_);
return v_res_1447_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(lean_object* v_as_1448_, lean_object* v_as_x27_1449_, lean_object* v_b_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_1449_, v_b_1450_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1448_ = stack[0].m_obj;
lean_object* v_as_x27_1449_ = stack[1].m_obj;
lean_object* v_b_1450_ = stack[2].m_obj;
lean_object* v___y_1452_ = stack[4].m_obj;
lean_object* v___y_1453_ = stack[5].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(v_as_1448_, v_as_x27_1449_, v_b_1450_, lean_box(0), v___y_1452_, v___y_1453_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___boxed(lean_object* v_as_1457_, lean_object* v_as_x27_1458_, lean_object* v_b_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(v_as_1457_, v_as_x27_1458_, v_b_1459_, v_a_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v_as_x27_1458_);
lean_dec(v_as_1457_);
return v_res_1464_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(lean_object* v_as_1465_, lean_object* v_as_x27_1466_, lean_object* v_b_1467_, lean_object* v_a_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_1466_, v_b_1467_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1465_ = stack[0].m_obj;
lean_object* v_as_x27_1466_ = stack[1].m_obj;
lean_object* v_b_1467_ = stack[2].m_obj;
lean_object* v___y_1469_ = stack[4].m_obj;
lean_object* v___y_1470_ = stack[5].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(v_as_1465_, v_as_x27_1466_, v_b_1467_, lean_box(0), v___y_1469_, v___y_1470_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___boxed(lean_object* v_as_1474_, lean_object* v_as_x27_1475_, lean_object* v_b_1476_, lean_object* v_a_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(v_as_1474_, v_as_x27_1475_, v_b_1476_, v_a_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v_as_x27_1475_);
lean_dec(v_as_1474_);
return v_res_1481_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(lean_object* v_as_1482_, lean_object* v_as_x27_1483_, lean_object* v_b_1484_, lean_object* v_a_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1483_, v_b_1484_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1482_ = stack[0].m_obj;
lean_object* v_as_x27_1483_ = stack[1].m_obj;
lean_object* v_b_1484_ = stack[2].m_obj;
lean_object* v___y_1486_ = stack[4].m_obj;
lean_object* v___y_1487_ = stack[5].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(v_as_1482_, v_as_x27_1483_, v_b_1484_, lean_box(0), v___y_1486_, v___y_1487_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___boxed(lean_object* v_as_1491_, lean_object* v_as_x27_1492_, lean_object* v_b_1493_, lean_object* v_a_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(v_as_1491_, v_as_x27_1492_, v_b_1493_, v_a_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v_as_x27_1492_);
lean_dec(v_as_1491_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4(lean_object* v_00_u03b2_1499_, lean_object* v_a_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1503_, lean_object* v_a_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4(v_00_u03b2_1503_, v_a_1504_, v_x_1505_);
lean_dec(v_x_1505_);
lean_dec(v_a_1504_);
return v_res_1506_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(lean_object* v_init_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_object* v_k_1514_; lean_object* v_l_1515_; lean_object* v_r_1516_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_k_1514_ = lean_ctor_get(v_x_1510_, 1);
lean_inc(v_k_1514_);
v_l_1515_ = lean_ctor_get(v_x_1510_, 3);
lean_inc(v_l_1515_);
v_r_1516_ = lean_ctor_get(v_x_1510_, 4);
lean_inc(v_r_1516_);
lean_dec_ref_known(v_x_1510_, 5);
v___x_1524_ = lean_box(0);
v___x_1525_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1509_, v_l_1515_, v___y_1511_, v___y_1512_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1525_, 0);
lean_dec(v_unused_1548_);
v___x_1527_ = v___x_1525_;
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v___x_1525_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_env_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_st_ref_get(v___y_1512_);
v_env_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc_ref(v_env_1530_);
lean_dec(v___x_1529_);
lean_inc(v_k_1514_);
v___x_1531_ = lean_environment_find(v_env_1530_, v_k_1514_);
if (lean_obj_tag(v___x_1531_) == 1)
{
lean_object* v_val_1532_; 
v_val_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v___x_1531_, 1);
if (lean_obj_tag(v_val_1532_) == 6)
{
lean_object* v_val_1533_; lean_object* v___x_1534_; 
v_val_1533_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_val_1533_);
lean_dec_ref_known(v_val_1532_, 1);
v___x_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v___y_1511_, v_k_1514_);
if (lean_obj_tag(v___x_1534_) == 1)
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1534_, 1);
if (lean_obj_tag(v_val_1535_) == 6)
{
lean_object* v_val_1536_; uint8_t v___x_1537_; 
v_val_1536_ = lean_ctor_get(v_val_1535_, 0);
lean_inc_ref(v_val_1536_);
lean_dec_ref_known(v_val_1535_, 1);
v___x_1537_ = l_Lean_instBEqConstructorVal_beq(v_val_1533_, v_val_1536_);
lean_dec_ref(v_val_1536_);
lean_dec_ref(v_val_1533_);
if (v___x_1537_ == 0)
{
uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_r_1516_);
v___x_1538_ = 1;
v___x_1539_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1));
v___x_1540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1514_, v___x_1538_);
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = lean_mk_io_user_error(v___x_1541_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 1);
lean_ctor_set(v___x_1527_, 0, v___x_1542_);
v___x_1544_ = v___x_1527_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
else
{
lean_del_object(v___x_1527_);
lean_dec(v_k_1514_);
v_init_1509_ = v___x_1524_;
v_x_1510_ = v_r_1516_;
goto _start;
}
}
else
{
lean_dec(v_val_1535_);
lean_dec_ref(v_val_1533_);
lean_del_object(v___x_1527_);
lean_dec(v_r_1516_);
goto v___jp_1517_;
}
}
else
{
lean_dec(v___x_1534_);
lean_dec_ref(v_val_1533_);
lean_del_object(v___x_1527_);
lean_dec(v_r_1516_);
goto v___jp_1517_;
}
}
else
{
lean_dec(v_val_1532_);
lean_del_object(v___x_1527_);
lean_dec(v_r_1516_);
goto v___jp_1517_;
}
}
else
{
lean_dec(v___x_1531_);
lean_del_object(v___x_1527_);
lean_dec(v_r_1516_);
goto v___jp_1517_;
}
}
}
else
{
lean_dec(v_r_1516_);
lean_dec(v_k_1514_);
return v___x_1525_;
}
v___jp_1517_:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1518_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0));
v___x_1519_ = 1;
v___x_1520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1514_, v___x_1519_);
v___x_1521_ = lean_string_append(v___x_1518_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = lean_mk_io_user_error(v___x_1521_);
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_init_1509_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1509_ = stack[0].m_obj;
lean_object* v_x_1510_ = stack[1].m_obj;
lean_object* v___y_1511_ = stack[2].m_obj;
lean_object* v___y_1512_ = stack[3].m_obj;
lean_object* v_res_1551_;
v_res_1551_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1509_, v_x_1510_, v___y_1511_, v___y_1512_);
stack->m_obj
 = v_res_1551_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object* v_init_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1552_, v_x_1553_, v___y_1554_, v___y_1555_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1557_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_postponedConstructors_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = lean_st_ref_get(v_a_1559_);
v_postponedConstructors_1562_ = lean_ctor_get(v___x_1561_, 3);
lean_inc(v_postponedConstructors_1562_);
lean_dec(v___x_1561_);
v___x_1563_ = lean_box(0);
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v___x_1563_, v_postponedConstructors_1562_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1564_, 0);
lean_dec(v_unused_1572_);
v___x_1566_ = v___x_1564_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v___x_1564_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1563_);
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1563_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1564_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1564_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1558_ = stack[0].m_obj;
lean_object* v_a_1559_ = stack[1].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_a_1558_, v_a_1559_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors___boxed(lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1585_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(lean_object* v_init_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
if (lean_obj_tag(v_x_1589_) == 0)
{
lean_object* v_k_1593_; lean_object* v_l_1594_; lean_object* v_r_1595_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_k_1593_ = lean_ctor_get(v_x_1589_, 1);
lean_inc(v_k_1593_);
v_l_1594_ = lean_ctor_get(v_x_1589_, 3);
lean_inc(v_l_1594_);
v_r_1595_ = lean_ctor_get(v_x_1589_, 4);
lean_inc(v_r_1595_);
lean_dec_ref_known(v_x_1589_, 5);
v___x_1603_ = lean_box(0);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1588_, v_l_1594_, v___y_1590_, v___y_1591_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1626_; 
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1627_);
v___x_1606_ = v___x_1604_;
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v___x_1604_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_st_ref_get(v___y_1591_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_ref(v_env_1609_);
lean_dec(v___x_1608_);
lean_inc(v_k_1593_);
v___x_1610_ = lean_environment_find(v_env_1609_, v_k_1593_);
if (lean_obj_tag(v___x_1610_) == 1)
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v___x_1610_, 1);
if (lean_obj_tag(v_val_1611_) == 7)
{
lean_object* v_val_1612_; lean_object* v___x_1613_; 
v_val_1612_ = lean_ctor_get(v_val_1611_, 0);
lean_inc_ref(v_val_1612_);
lean_dec_ref_known(v_val_1611_, 1);
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v___y_1590_, v_k_1593_);
if (lean_obj_tag(v___x_1613_) == 1)
{
lean_object* v_val_1614_; 
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (lean_obj_tag(v_val_1614_) == 7)
{
lean_object* v_val_1615_; uint8_t v___x_1616_; 
v_val_1615_ = lean_ctor_get(v_val_1614_, 0);
lean_inc_ref(v_val_1615_);
lean_dec_ref_known(v_val_1614_, 1);
v___x_1616_ = l_Lean_instBEqRecursorVal_beq(v_val_1612_, v_val_1615_);
lean_dec_ref(v_val_1615_);
lean_dec_ref(v_val_1612_);
if (v___x_1616_ == 0)
{
uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_dec(v_r_1595_);
v___x_1617_ = 1;
v___x_1618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1));
v___x_1619_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1593_, v___x_1617_);
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = lean_mk_io_user_error(v___x_1620_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 1);
lean_ctor_set(v___x_1606_, 0, v___x_1621_);
v___x_1623_ = v___x_1606_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
else
{
lean_del_object(v___x_1606_);
lean_dec(v_k_1593_);
v_init_1588_ = v___x_1603_;
v_x_1589_ = v_r_1595_;
goto _start;
}
}
else
{
lean_dec(v_val_1614_);
lean_dec_ref(v_val_1612_);
lean_del_object(v___x_1606_);
lean_dec(v_r_1595_);
goto v___jp_1596_;
}
}
else
{
lean_dec(v___x_1613_);
lean_dec_ref(v_val_1612_);
lean_del_object(v___x_1606_);
lean_dec(v_r_1595_);
goto v___jp_1596_;
}
}
else
{
lean_dec(v_val_1611_);
lean_del_object(v___x_1606_);
lean_dec(v_r_1595_);
goto v___jp_1596_;
}
}
else
{
lean_dec(v___x_1610_);
lean_del_object(v___x_1606_);
lean_dec(v_r_1595_);
goto v___jp_1596_;
}
}
}
else
{
lean_dec(v_r_1595_);
lean_dec(v_k_1593_);
return v___x_1604_;
}
v___jp_1596_:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1597_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0));
v___x_1598_ = 1;
v___x_1599_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1593_, v___x_1598_);
v___x_1600_ = lean_string_append(v___x_1597_, v___x_1599_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = lean_mk_io_user_error(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_init_1588_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1588_ = stack[0].m_obj;
lean_object* v_x_1589_ = stack[1].m_obj;
lean_object* v___y_1590_ = stack[2].m_obj;
lean_object* v___y_1591_ = stack[3].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1588_, v_x_1589_, v___y_1590_, v___y_1591_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object* v_init_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1631_, v_x_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1636_;
}
}
lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_postponedRecursors_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_st_ref_get(v_a_1638_);
v_postponedRecursors_1641_ = lean_ctor_get(v___x_1640_, 4);
lean_inc(v_postponedRecursors_1641_);
lean_dec(v___x_1640_);
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v___x_1642_, v_postponedRecursors_1641_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1643_, 0);
lean_dec(v_unused_1651_);
v___x_1645_ = v___x_1643_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v___x_1643_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1642_);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1642_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1643_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1643_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1637_ = stack[0].m_obj;
lean_object* v_a_1638_ = stack[1].m_obj;
lean_object* v_res_1660_;
v_res_1660_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_a_1637_, v_a_1638_);
stack->m_obj
 = v_res_1660_;
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors___boxed(lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_inc(v_x_1665_);
return v_x_1665_;
}
else
{
lean_object* v_key_1667_; lean_object* v_value_1668_; lean_object* v_tail_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_key_1667_ = lean_ctor_get(v_x_1666_, 0);
v_value_1668_ = lean_ctor_get(v_x_1666_, 1);
v_tail_1669_ = lean_ctor_get(v_x_1666_, 2);
v___x_1670_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1665_, v_tail_1669_);
lean_inc(v_value_1668_);
lean_inc(v_key_1667_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_key_1667_);
lean_ctor_set(v___x_1671_, 1, v_value_1668_);
v___x_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1___boxed(lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1673_, v_x_1674_);
lean_dec(v_x_1674_);
lean_dec(v_x_1673_);
return v_res_1675_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_eq(v_i_1677_, v_stop_1678_);
if (v___x_1680_ == 0)
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = ((size_t)1ULL);
v___x_1682_ = lean_usize_sub(v_i_1677_, v___x_1681_);
v___x_1683_ = lean_array_uget_borrowed(v_as_1676_, v___x_1682_);
v___x_1684_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_b_1679_, v___x_1683_);
lean_dec(v_b_1679_);
v_i_1677_ = v___x_1682_;
v_b_1679_ = v___x_1684_;
goto _start;
}
else
{
return v_b_1679_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1676_ = stack[0].m_obj;
size_t v_i_1677_ = stack[1].m_num;
size_t v_stop_1678_ = stack[2].m_num;
lean_object* v_b_1679_ = stack[3].m_obj;
lean_object* v_res_1686_;
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_as_1676_, v_i_1677_, v_stop_1678_, v_b_1679_);
stack->m_obj
 = v_res_1686_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2___boxed(lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_, lean_object* v_b_1690_){
_start:
{
size_t v_i_boxed_1691_; size_t v_stop_boxed_1692_; lean_object* v_res_1693_; 
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1692_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_as_1687_, v_i_boxed_1691_, v_stop_boxed_1692_, v_b_1690_);
lean_dec_ref(v_as_1687_);
return v_res_1693_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(lean_object* v_as_x27_1694_, lean_object* v_b_1695_){
_start:
{
if (lean_obj_tag(v_as_x27_1694_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_b_1695_);
return v___x_1697_;
}
else
{
lean_object* v_head_1698_; lean_object* v_tail_1699_; lean_object* v_fst_1700_; lean_object* v_snd_1701_; uint8_t v___x_1702_; 
v_head_1698_ = lean_ctor_get(v_as_x27_1694_, 0);
v_tail_1699_ = lean_ctor_get(v_as_x27_1694_, 1);
v_fst_1700_ = lean_ctor_get(v_head_1698_, 0);
v_snd_1701_ = lean_ctor_get(v_head_1698_, 1);
v___x_1702_ = l_Lean_ConstantInfo_isUnsafe(v_snd_1701_);
if (v___x_1702_ == 0)
{
uint8_t v___x_1703_; 
v___x_1703_ = l_Lean_ConstantInfo_isPartial(v_snd_1701_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_inc(v_fst_1700_);
v___x_1704_ = l_Lean_NameSet_insert(v_b_1695_, v_fst_1700_);
v_as_x27_1694_ = v_tail_1699_;
v_b_1695_ = v___x_1704_;
goto _start;
}
else
{
v_as_x27_1694_ = v_tail_1699_;
goto _start;
}
}
else
{
v_as_x27_1694_ = v_tail_1699_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1694_ = stack[0].m_obj;
lean_object* v_b_1695_ = stack[1].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1694_, v_b_1695_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___boxed(lean_object* v_as_x27_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1709_, v_b_1710_);
lean_dec(v_as_x27_1709_);
return v_res_1712_;
}
}
lean_object* l_Lean_Kernel_Environment_replay(lean_object* v_newConstants_1713_, lean_object* v_env_1714_){
_start:
{
lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v_buckets_1737_; lean_object* v_remaining_1738_; lean_object* v___y_1740_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_buckets_1737_ = lean_ctor_get(v_newConstants_1713_, 1);
v_remaining_1738_ = l_Lean_NameSet_empty;
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_array_get_size(v_buckets_1737_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_nat_dec_lt(v___x_1759_, v___x_1758_);
if (v___x_1760_ == 0)
{
v___y_1740_ = v___x_1757_;
goto v___jp_1739_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_usize_of_nat(v___x_1758_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_1737_, v___x_1761_, v___x_1762_, v___x_1757_);
v___y_1740_ = v___x_1763_;
goto v___jp_1739_;
}
v___jp_1716_:
{
if (lean_obj_tag(v___y_1718_) == 0)
{
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v_isSharedCheck_1727_ = !lean_is_exclusive(v___y_1718_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___y_1718_, 0);
lean_dec(v_unused_1728_);
v___x_1720_ = v___y_1718_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v___y_1718_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v_env_1723_; lean_object* v___x_1725_; 
v___x_1722_ = lean_st_ref_get(v___y_1717_);
lean_dec(v___y_1717_);
v_env_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc_ref(v_env_1723_);
lean_dec(v___x_1722_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v_env_1723_);
v___x_1725_ = v___x_1720_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_env_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v___y_1717_);
v_a_1729_ = lean_ctor_get(v___y_1718_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___y_1718_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___y_1718_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___y_1718_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
v___jp_1739_:
{
lean_object* v___x_1741_; lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1741_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v___y_1740_, v_remaining_1738_);
lean_dec(v___y_1740_);
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_n(v_a_1742_, 2);
lean_dec_ref(v___x_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1744_, 0, v_env_1714_);
lean_ctor_set(v___x_1744_, 1, v_a_1742_);
lean_ctor_set(v___x_1744_, 2, v_remaining_1738_);
lean_ctor_set(v___x_1744_, 3, v_remaining_1738_);
lean_ctor_set(v___x_1744_, 4, v_remaining_1738_);
v___x_1745_ = lean_st_mk_ref(v___x_1744_);
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v___x_1743_, v_a_1742_, v_newConstants_1713_, v___x_1745_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_newConstants_1713_, v___x_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1748_; 
lean_dec_ref_known(v___x_1747_, 1);
v___x_1748_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_newConstants_1713_, v___x_1745_);
v___y_1717_ = v___x_1745_;
v___y_1718_ = v___x_1748_;
goto v___jp_1716_;
}
else
{
v___y_1717_ = v___x_1745_;
v___y_1718_ = v___x_1747_;
goto v___jp_1716_;
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v___x_1745_);
v_a_1749_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1746_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1746_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Kernel_Environment_replay_0interp(lean_interpreter_value* stack)
{
lean_object* v_newConstants_1713_ = stack[0].m_obj;
lean_object* v_env_1714_ = stack[1].m_obj;
lean_object* v_res_1764_;
v_res_1764_ = l_Lean_Kernel_Environment_replay(v_newConstants_1713_, v_env_1714_);
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay___boxed(lean_object* v_newConstants_1765_, lean_object* v_env_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Kernel_Environment_replay(v_newConstants_1765_, v_env_1766_);
lean_dec_ref(v_newConstants_1765_);
return v_res_1768_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(lean_object* v_as_1769_, lean_object* v_as_x27_1770_, lean_object* v_b_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1770_, v_b_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1769_ = stack[0].m_obj;
lean_object* v_as_x27_1770_ = stack[1].m_obj;
lean_object* v_b_1771_ = stack[2].m_obj;
lean_object* v_res_1775_;
v_res_1775_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(v_as_1769_, v_as_x27_1770_, v_b_1771_, lean_box(0));
stack->m_obj
 = v_res_1775_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___boxed(lean_object* v_as_1776_, lean_object* v_as_x27_1777_, lean_object* v_b_1778_, lean_object* v_a_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(v_as_1776_, v_as_x27_1777_, v_b_1778_, v_a_1779_);
lean_dec(v_as_x27_1777_);
lean_dec(v_as_1776_);
return v_res_1781_;
}
}
lean_object* l_Lean_Environment_replay(lean_object* v_newConstants_1782_, lean_object* v_env_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_elab_environment_to_kernel_env(v_env_1783_);
v___x_1786_ = l_Lean_Kernel_Environment_replay(v_newConstants_1782_, v___x_1785_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = l_Lean_Environment_ofKernelEnv(v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
v_a_1796_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1786_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1786_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Environment_replay_0interp(lean_interpreter_value* stack)
{
lean_object* v_newConstants_1782_ = stack[0].m_obj;
lean_object* v_env_1783_ = stack[1].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_Environment_replay(v_newConstants_1782_, v_env_1783_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay___boxed(lean_object* v_newConstants_1805_, lean_object* v_env_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Environment_replay(v_newConstants_1805_, v_env_1806_);
lean_dec_ref(v_newConstants_1805_);
return v_res_1808_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_FoldConsts(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Replay(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_FoldConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Replay(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Replay(uint8_t builtin) {
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
res = runtime_initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Replay(builtin);
}
#ifdef __cplusplus
}
#endif
