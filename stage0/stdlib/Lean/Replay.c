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
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_elab_environment_of_kernel_env(lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object*, lean_object*);
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
lean_inc(v_size_13_);
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
lean_dec(v_size_13_);
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
lean_dec(v_size_13_);
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
v___x_48_ = lean_nat_add(v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec(v___y_46_);
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
lean_ctor_set(v___x_28_, 3, v___y_45_);
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
lean_ctor_set(v_reuseFailAlloc_53_, 3, v___y_45_);
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
v___y_45_ = v___x_59_;
v___y_46_ = v___x_60_;
v___y_47_ = v_size_61_;
goto v___jp_44_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___y_45_ = v___x_59_;
v___y_46_ = v___x_60_;
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
lean_dec(v_size_13_);
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
lean_inc(v_size_96_);
v___x_97_ = lean_nat_add(v___x_12_, v_size_96_);
lean_dec(v_size_96_);
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
lean_inc(v_tree_201_);
if (lean_obj_tag(v_tree_201_) == 0)
{
lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v_size_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
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
v___x_375_ = lean_nat_add(v___y_372_, v___y_374_);
lean_dec(v___y_374_);
lean_dec(v___y_372_);
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
lean_ctor_set(v___x_379_, 3, v___y_373_);
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
lean_ctor_set(v_reuseFailAlloc_383_, 3, v___y_373_);
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
v___y_372_ = v___x_397_;
v___y_373_ = v___x_396_;
v___y_374_ = v_size_398_;
goto v___jp_371_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___y_372_ = v___x_397_;
v___y_373_ = v___x_396_;
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
lean_inc(v_size_498_);
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
lean_dec(v_size_498_);
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
lean_dec(v_size_498_);
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
lean_dec(v_size_498_);
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
lean_inc(v_size_583_);
v___x_584_ = lean_nat_add(v___x_497_, v_size_583_);
lean_dec(v_size_583_);
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
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(lean_object* v_name_665_, lean_object* v_a_666_){
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
v___x_686_ = lean_st_ref_set(v_a_666_, v___x_685_);
v___x_687_ = lean_box(v___x_670_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg___boxed(lean_object* v_name_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_691_, v_a_692_);
lean_dec(v_a_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(lean_object* v_name_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_695_, v_a_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___boxed(lean_object* v_name_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo(v_name_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0(lean_object* v_00_u03b2_705_, lean_object* v_k_706_, lean_object* v_t_707_, lean_object* v_h_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_k_706_, v_t_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___boxed(lean_object* v_00_u03b2_710_, lean_object* v_k_711_, lean_object* v_t_712_, lean_object* v_h_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0(v_00_u03b2_710_, v_k_711_, v_t_712_, v_h_713_);
lean_dec(v_k_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(lean_object* v_ex_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_717_ = l_Lean_Options_empty;
v___x_718_ = l_Lean_Kernel_Exception_toMessageData(v_ex_715_, v___x_717_);
v___x_719_ = l_Lean_MessageData_toString(v___x_718_);
v___x_720_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg___boxed(lean_object* v_ex_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_ex_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(lean_object* v_ex_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_ex_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___boxed(lean_object* v_ex_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException(v_ex_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(lean_object* v_d_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; lean_object* v_env_739_; size_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_738_ = lean_st_ref_get(v_a_736_);
v_env_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_env_739_);
lean_dec(v___x_738_);
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_box(0);
v___x_742_ = lean_add_decl(v_env_739_, v___x_740_, v___x_740_, v_d_735_, v___x_741_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_throwKernelException___redArg(v_a_743_);
return v___x_744_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_767_; 
v_a_745_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_767_ == 0)
{
v___x_747_ = v___x_742_;
v_isShared_748_ = v_isSharedCheck_767_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_767_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v_remaining_750_; lean_object* v_pending_751_; lean_object* v_postponedConstructors_752_; lean_object* v_postponedRecursors_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_765_; 
v___x_749_ = lean_st_ref_take(v_a_736_);
v_remaining_750_ = lean_ctor_get(v___x_749_, 1);
v_pending_751_ = lean_ctor_get(v___x_749_, 2);
v_postponedConstructors_752_ = lean_ctor_get(v___x_749_, 3);
v_postponedRecursors_753_ = lean_ctor_get(v___x_749_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_749_, 0);
lean_dec(v_unused_766_);
v___x_755_ = v___x_749_;
v_isShared_756_ = v_isSharedCheck_765_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_postponedRecursors_753_);
lean_inc(v_postponedConstructors_752_);
lean_inc(v_pending_751_);
lean_inc(v_remaining_750_);
lean_dec(v___x_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_765_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_745_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_remaining_750_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_pending_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_postponedConstructors_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_postponedRecursors_753_);
v___x_758_ = v_reuseFailAlloc_764_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_759_ = lean_st_ref_set(v_a_736_, v___x_758_);
v___x_760_ = lean_box(0);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 0, v___x_760_);
v___x_762_ = v___x_747_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg___boxed(lean_object* v_d_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v_d_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec(v_d_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(lean_object* v_d_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v_d_772_, v_a_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___boxed(lean_object* v_d_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl(v_d_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_d_777_);
return v_res_781_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_instMonadEIO(lean_box(0));
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___f_791_; lean_object* v___x_32059__overap_792_; lean_object* v___x_793_; 
v___x_787_ = lean_obj_once(&l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0, &l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0_once, _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___closed__0);
v___x_788_ = l_StateRefT_x27_instMonad___redArg(v___x_787_);
v___x_789_ = lean_box(0);
v___x_790_ = l_instInhabitedOfMonad___redArg(v___x_788_, v___x_789_);
v___f_791_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_791_, 0, v___x_790_);
v___x_32059__overap_792_ = lean_panic_fn_borrowed(v___f_791_, v_msg_783_);
lean_dec_ref(v___f_791_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
v___x_793_ = lean_apply_3(v___x_32059__overap_792_, v___y_784_, v___y_785_, lean_box(0));
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___boxed(lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v_msg_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(lean_object* v_name_801_, lean_object* v_____r_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_env_807_; lean_object* v_remaining_808_; lean_object* v_pending_809_; lean_object* v_postponedConstructors_810_; lean_object* v_postponedRecursors_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_822_; 
v___x_806_ = lean_st_ref_take(v___y_804_);
v_env_807_ = lean_ctor_get(v___x_806_, 0);
v_remaining_808_ = lean_ctor_get(v___x_806_, 1);
v_pending_809_ = lean_ctor_get(v___x_806_, 2);
v_postponedConstructors_810_ = lean_ctor_get(v___x_806_, 3);
v_postponedRecursors_811_ = lean_ctor_get(v___x_806_, 4);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_822_ == 0)
{
v___x_813_ = v___x_806_;
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_postponedRecursors_811_);
lean_inc(v_postponedConstructors_810_);
lean_inc(v_pending_809_);
lean_inc(v_remaining_808_);
lean_inc(v_env_807_);
lean_dec(v___x_806_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_801_, v_pending_809_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 2, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_env_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_remaining_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_postponedConstructors_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_postponedRecursors_811_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_st_ref_set(v___y_804_, v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0));
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed(lean_object* v_name_823_, lean_object* v_____r_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_823_, v_____r_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_name_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(lean_object* v_val_829_, lean_object* v___f_830_, lean_object* v_____r_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_835_, 0, v_val_829_);
v___x_836_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_835_, v___y_833_);
lean_dec_ref_known(v___x_835_, 1);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v___x_838_ = lean_apply_4(v___f_830_, v_a_837_, v___y_832_, v___y_833_, lean_box(0));
return v___x_838_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v___f_830_);
v_a_839_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_836_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_836_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed(lean_object* v_val_847_, lean_object* v___f_848_, lean_object* v_____r_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_847_, v___f_848_, v_____r_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(lean_object* v___f_854_, lean_object* v_x_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_860_ = lean_apply_4(v___f_854_, v___x_859_, v___y_856_, v___y_857_, lean_box(0));
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2___boxed(lean_object* v___f_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_861_, v_x_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v_x_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(lean_object* v_a_867_, lean_object* v_x_868_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v___x_869_; 
v___x_869_ = lean_box(0);
return v___x_869_;
}
else
{
lean_object* v_key_870_; lean_object* v_value_871_; lean_object* v_tail_872_; uint8_t v___x_873_; 
v_key_870_ = lean_ctor_get(v_x_868_, 0);
v_value_871_ = lean_ctor_get(v_x_868_, 1);
v_tail_872_ = lean_ctor_get(v_x_868_, 2);
v___x_873_ = lean_name_eq(v_key_870_, v_a_867_);
if (v___x_873_ == 0)
{
v_x_868_ = v_tail_872_;
goto _start;
}
else
{
lean_object* v___x_875_; 
lean_inc(v_value_871_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v_value_871_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg___boxed(lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_876_, v_x_877_);
lean_dec(v_x_877_);
lean_dec(v_a_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_buckets_881_; lean_object* v___x_882_; uint64_t v___y_884_; 
v_buckets_881_ = lean_ctor_get(v_m_879_, 1);
v___x_882_ = lean_array_get_size(v_buckets_881_);
if (lean_obj_tag(v_a_880_) == 0)
{
uint64_t v___x_898_; 
v___x_898_ = 1723ULL;
v___y_884_ = v___x_898_;
goto v___jp_883_;
}
else
{
uint64_t v_hash_899_; 
v_hash_899_ = lean_ctor_get_uint64(v_a_880_, sizeof(void*)*2);
v___y_884_ = v_hash_899_;
goto v___jp_883_;
}
v___jp_883_:
{
uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v_fold_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_885_ = 32ULL;
v___x_886_ = lean_uint64_shift_right(v___y_884_, v___x_885_);
v_fold_887_ = lean_uint64_xor(v___y_884_, v___x_886_);
v___x_888_ = 16ULL;
v___x_889_ = lean_uint64_shift_right(v_fold_887_, v___x_888_);
v___x_890_ = lean_uint64_xor(v_fold_887_, v___x_889_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = lean_usize_of_nat(v___x_882_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_sub(v___x_892_, v___x_893_);
v___x_895_ = lean_usize_land(v___x_891_, v___x_894_);
v___x_896_ = lean_array_uget_borrowed(v_buckets_881_, v___x_895_);
v___x_897_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_880_, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg___boxed(lean_object* v_m_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_m_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_m_900_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
if (lean_obj_tag(v_x_904_) == 0)
{
uint8_t v___x_905_; 
v___x_905_ = 1;
return v___x_905_;
}
else
{
uint8_t v___x_906_; 
v___x_906_ = 0;
return v___x_906_;
}
}
else
{
if (lean_obj_tag(v_x_904_) == 0)
{
uint8_t v___x_907_; 
v___x_907_ = 0;
return v___x_907_;
}
else
{
lean_object* v_head_908_; lean_object* v_tail_909_; lean_object* v_head_910_; lean_object* v_tail_911_; uint8_t v___x_912_; 
v_head_908_ = lean_ctor_get(v_x_903_, 0);
v_tail_909_ = lean_ctor_get(v_x_903_, 1);
v_head_910_ = lean_ctor_get(v_x_904_, 0);
v_tail_911_ = lean_ctor_get(v_x_904_, 1);
v___x_912_ = lean_name_eq(v_head_908_, v_head_910_);
if (v___x_912_ == 0)
{
return v___x_912_;
}
else
{
v_x_903_ = v_tail_909_;
v_x_904_ = v_tail_911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4___boxed(lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_x_914_, v_x_915_);
lean_dec(v_x_915_);
lean_dec(v_x_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(lean_object* v_as_x27_918_, lean_object* v_b_919_, lean_object* v___y_920_){
_start:
{
if (lean_obj_tag(v_as_x27_918_) == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_b_919_);
return v___x_922_;
}
else
{
lean_object* v_head_923_; lean_object* v_tail_924_; lean_object* v___x_925_; lean_object* v_env_926_; lean_object* v_remaining_927_; lean_object* v_pending_928_; lean_object* v_postponedConstructors_929_; lean_object* v_postponedRecursors_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_943_; 
v_head_923_ = lean_ctor_get(v_as_x27_918_, 0);
v_tail_924_ = lean_ctor_get(v_as_x27_918_, 1);
v___x_925_ = lean_st_ref_take(v___y_920_);
v_env_926_ = lean_ctor_get(v___x_925_, 0);
v_remaining_927_ = lean_ctor_get(v___x_925_, 1);
v_pending_928_ = lean_ctor_get(v___x_925_, 2);
v_postponedConstructors_929_ = lean_ctor_get(v___x_925_, 3);
v_postponedRecursors_930_ = lean_ctor_get(v___x_925_, 4);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_943_ == 0)
{
v___x_932_ = v___x_925_;
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_postponedRecursors_930_);
lean_inc(v_postponedConstructors_929_);
lean_inc(v_pending_928_);
lean_inc(v_remaining_927_);
lean_inc(v_env_926_);
lean_dec(v___x_925_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_943_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_934_ = l_Lean_ConstantInfo_name(v_head_923_);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v___x_934_, v_remaining_927_);
v___x_936_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v___x_934_, v_pending_928_);
lean_dec(v___x_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 2, v___x_936_);
lean_ctor_set(v___x_932_, 1, v___x_935_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_env_926_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_postponedConstructors_929_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_postponedRecursors_930_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_st_ref_set(v___y_920_, v___x_938_);
v___x_940_ = lean_box(0);
v_as_x27_918_ = v_tail_924_;
v_b_919_ = v___x_940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg___boxed(lean_object* v_as_x27_944_, lean_object* v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_944_, v_b_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec(v_as_x27_944_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(lean_object* v_msg_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l_Lean_instInhabitedConstantInfo_default;
v___x_951_ = lean_panic_fn_borrowed(v___x_950_, v_msg_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__2));
v___x_956_ = lean_unsigned_to_nat(11u);
v___x_957_ = lean_unsigned_to_nat(163u);
v___x_958_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__1));
v___x_959_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__0));
v___x_960_ = l_mkPanicMessageWithDecl(v___x_959_, v___x_958_, v___x_957_, v___x_956_, v___x_955_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0(lean_object* v_a_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___closed__3);
v___x_964_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0_spec__3(v___x_963_);
return v___x_964_;
}
else
{
lean_object* v_key_965_; lean_object* v_value_966_; lean_object* v_tail_967_; uint8_t v___x_968_; 
v_key_965_ = lean_ctor_get(v_x_962_, 0);
v_value_966_ = lean_ctor_get(v_x_962_, 1);
v_tail_967_ = lean_ctor_get(v_x_962_, 2);
v___x_968_ = lean_name_eq(v_key_965_, v_a_961_);
if (v___x_968_ == 0)
{
v_x_962_ = v_tail_967_;
goto _start;
}
else
{
lean_inc(v_value_966_);
return v_value_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0___boxed(lean_object* v_a_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0(v_a_970_, v_x_971_);
lean_dec(v_x_971_);
lean_dec(v_a_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_buckets_975_; lean_object* v___x_976_; uint64_t v___y_978_; 
v_buckets_975_ = lean_ctor_get(v_m_973_, 1);
v___x_976_ = lean_array_get_size(v_buckets_975_);
if (lean_obj_tag(v_a_974_) == 0)
{
uint64_t v___x_992_; 
v___x_992_ = 1723ULL;
v___y_978_ = v___x_992_;
goto v___jp_977_;
}
else
{
uint64_t v_hash_993_; 
v_hash_993_ = lean_ctor_get_uint64(v_a_974_, sizeof(void*)*2);
v___y_978_ = v_hash_993_;
goto v___jp_977_;
}
v___jp_977_:
{
uint64_t v___x_979_; uint64_t v___x_980_; uint64_t v_fold_981_; uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; size_t v___x_985_; size_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_979_ = 32ULL;
v___x_980_ = lean_uint64_shift_right(v___y_978_, v___x_979_);
v_fold_981_ = lean_uint64_xor(v___y_978_, v___x_980_);
v___x_982_ = 16ULL;
v___x_983_ = lean_uint64_shift_right(v_fold_981_, v___x_982_);
v___x_984_ = lean_uint64_xor(v_fold_981_, v___x_983_);
v___x_985_ = lean_uint64_to_usize(v___x_984_);
v___x_986_ = lean_usize_of_nat(v___x_976_);
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_sub(v___x_986_, v___x_987_);
v___x_989_ = lean_usize_land(v___x_985_, v___x_988_);
v___x_990_ = lean_array_uget_borrowed(v_buckets_975_, v___x_989_);
v___x_991_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0_spec__0(v_a_974_, v___x_990_);
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0___boxed(lean_object* v_m_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(v_m_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_m_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v___y_999_){
_start:
{
if (lean_obj_tag(v_x_997_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = l_List_reverse___redArg(v_x_998_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
else
{
lean_object* v_head_1003_; lean_object* v_tail_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1013_; 
v_head_1003_ = lean_ctor_get(v_x_997_, 0);
v_tail_1004_ = lean_ctor_get(v_x_997_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_997_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1006_ = v_x_997_;
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_tail_1004_);
lean_inc(v_head_1003_);
lean_dec(v_x_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(v___y_999_, v_head_1003_);
lean_dec(v_head_1003_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_x_998_);
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_x_998_);
v___x_1010_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v_x_997_ = v_tail_1004_;
v_x_998_ = v___x_1010_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_x_1014_, v_x_1015_, v___y_1016_);
lean_dec_ref(v___y_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l_List_reverse___redArg(v_x_1020_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
else
{
lean_object* v_head_1026_; lean_object* v_tail_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1041_; 
v_head_1026_ = lean_ctor_get(v_x_1019_, 0);
v_tail_1027_ = lean_ctor_get(v_x_1019_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1029_ = v_x_1019_;
v_isShared_1030_ = v_isSharedCheck_1041_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_tail_1027_);
lean_inc(v_head_1026_);
lean_dec(v_x_1019_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1041_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v_ctors_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1031_ = l_Lean_ConstantInfo_inductiveVal_x21(v_head_1026_);
v_ctors_1032_ = lean_ctor_get(v___x_1031_, 4);
lean_inc(v_ctors_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_ctors_1032_, v___x_1033_, v___y_1021_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_head_1026_);
lean_ctor_set(v___x_1036_, 1, v_a_1035_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v_x_1020_);
lean_ctor_set(v___x_1029_, 0, v___x_1036_);
v___x_1038_ = v___x_1029_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_x_1020_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
v_x_1019_ = v_tail_1027_;
v_x_1020_ = v___x_1038_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_x_1042_, v_x_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
if (lean_obj_tag(v_a_1048_) == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_List_reverse___redArg(v_a_1049_);
return v___x_1050_;
}
else
{
lean_object* v_head_1051_; lean_object* v_tail_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1063_; 
v_head_1051_ = lean_ctor_get(v_a_1048_, 0);
v_tail_1052_ = lean_ctor_get(v_a_1048_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_a_1048_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1054_ = v_a_1048_;
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_tail_1052_);
lean_inc(v_head_1051_);
lean_dec(v_a_1048_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1063_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1056_ = l_Lean_ConstantInfo_name(v_head_1051_);
v___x_1057_ = l_Lean_ConstantInfo_type(v_head_1051_);
lean_dec(v_head_1051_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_a_1049_);
lean_ctor_set(v___x_1054_, 0, v___x_1058_);
v___x_1060_ = v___x_1054_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_a_1049_);
v___x_1060_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v_a_1048_ = v_tail_1052_;
v_a_1049_ = v___x_1060_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
if (lean_obj_tag(v_a_1064_) == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = l_List_reverse___redArg(v_a_1065_);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1083_; 
v_head_1067_ = lean_ctor_get(v_a_1064_, 0);
v_tail_1068_ = lean_ctor_get(v_a_1064_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_a_1064_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1070_ = v_a_1064_;
v_isShared_1071_ = v_isSharedCheck_1083_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_tail_1068_);
lean_inc(v_head_1067_);
lean_dec(v_a_1064_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1083_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_fst_1072_ = lean_ctor_get(v_head_1067_, 0);
lean_inc(v_fst_1072_);
v_snd_1073_ = lean_ctor_get(v_head_1067_, 1);
lean_inc(v_snd_1073_);
lean_dec(v_head_1067_);
v___x_1074_ = l_Lean_ConstantInfo_name(v_fst_1072_);
v___x_1075_ = l_Lean_ConstantInfo_type(v_fst_1072_);
lean_dec(v_fst_1072_);
v___x_1076_ = lean_box(0);
v___x_1077_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(v_snd_1073_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1075_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_a_1065_);
lean_ctor_set(v___x_1070_, 0, v___x_1078_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1065_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_a_1064_ = v_tail_1068_;
v_a_1065_ = v___x_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(lean_object* v_as_x27_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
if (lean_obj_tag(v_as_x27_1089_) == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1090_);
return v___x_1094_;
}
else
{
lean_object* v_head_1095_; lean_object* v_tail_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_head_1095_ = lean_ctor_get(v_as_x27_1089_, 0);
v_tail_1096_ = lean_ctor_get(v_as_x27_1089_, 1);
lean_inc(v_head_1095_);
v___x_1097_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_1095_);
v___x_1098_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1097_, v___y_1091_, v___y_1092_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = lean_box(0);
v_as_x27_1089_ = v_tail_1096_;
v_b_1090_ = v___x_1099_;
goto _start;
}
else
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(lean_object* v_as_x27_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
if (lean_obj_tag(v_as_x27_1101_) == 0)
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_b_1102_);
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; lean_object* v_snd_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_head_1107_ = lean_ctor_get(v_as_x27_1101_, 0);
v_tail_1108_ = lean_ctor_get(v_as_x27_1101_, 1);
v_snd_1109_ = lean_ctor_get(v_head_1107_, 1);
v___x_1110_ = lean_box(0);
v___x_1111_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_snd_1109_, v___x_1110_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_dec_ref_known(v___x_1111_, 1);
v_as_x27_1101_ = v_tail_1108_;
v_b_1102_ = v___x_1110_;
goto _start;
}
else
{
return v___x_1111_;
}
}
}
}
static lean_object* _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1116_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6));
v___x_1117_ = lean_unsigned_to_nat(50u);
v___x_1118_ = lean_unsigned_to_nat(76u);
v___x_1119_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5));
v___x_1120_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4));
v___x_1121_ = l_mkPanicMessageWithDecl(v___x_1120_, v___x_1119_, v___x_1118_, v___x_1117_, v___x_1116_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(lean_object* v_name_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; 
lean_inc(v_name_1122_);
v___x_1126_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_1122_, v_a_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1327_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1327_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1327_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_unbox(v_a_1127_);
lean_dec(v_a_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec(v_name_1122_);
v___x_1132_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_a_1123_, v_name_1122_);
if (lean_obj_tag(v___x_1136_) == 1)
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1324_; 
v_val_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1324_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1324_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc(v_val_1137_);
v___x_1141_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_1137_);
v___x_1142_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1141_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1322_; 
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1142_, 0);
lean_dec(v_unused_1323_);
v___x_1144_ = v___x_1142_;
v_isShared_1145_ = v_isSharedCheck_1322_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v___x_1142_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1322_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v_pending_1147_; uint8_t v___x_1148_; lean_object* v_a_1150_; lean_object* v___y_1165_; 
v___x_1146_ = lean_st_ref_get(v_a_1124_);
v_pending_1147_ = lean_ctor_get(v___x_1146_, 2);
lean_inc(v_pending_1147_);
lean_dec(v___x_1146_);
v___x_1148_ = l_Lean_NameSet_contains(v_pending_1147_, v_name_1122_);
lean_dec(v_pending_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_del_object(v___x_1144_);
lean_del_object(v___x_1139_);
lean_dec(v_val_1137_);
lean_dec(v_name_1122_);
v___x_1176_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1176_);
v___x_1178_ = v___x_1129_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
else
{
lean_object* v___f_1180_; 
lean_inc(v_name_1122_);
v___f_1180_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1180_, 0, v_name_1122_);
switch(lean_obj_tag(v_val_1137_))
{
case 0:
{
lean_object* v_val_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1181_ = lean_ctor_get(v_val_1137_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_val_1137_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1183_ = v_val_1137_;
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_val_1181_);
lean_dec(v_val_1137_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_val_1181_);
v___x_1186_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1186_, v_a_1124_);
lean_dec_ref(v___x_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v_a_1188_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1189_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1190_; 
v_a_1190_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1187_, 1);
v_a_1150_ = v_a_1190_;
goto v___jp_1149_;
}
}
}
}
case 1:
{
lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1193_ = lean_ctor_get(v_val_1137_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_val_1137_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1195_ = v_val_1137_;
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_dec(v_val_1137_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_val_1193_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; 
v___x_1199_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1198_, v_a_1124_);
lean_dec_ref(v___x_1198_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v_a_1200_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1201_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1202_; 
v_a_1202_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1199_, 1);
v_a_1150_ = v_a_1202_;
goto v___jp_1149_;
}
}
}
}
case 2:
{
lean_object* v_val_1205_; lean_object* v___x_1206_; lean_object* v_env_1207_; lean_object* v___f_1208_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_val_1205_ = lean_ctor_get(v_val_1137_, 0);
lean_inc_ref_n(v_val_1205_, 2);
v___x_1206_ = lean_st_ref_get(v_a_1124_);
v_env_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_env_1207_);
lean_dec(v___x_1206_);
lean_inc_ref(v___f_1180_);
v___f_1208_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(v___f_1208_, 0, v_val_1205_);
lean_closure_set(v___f_1208_, 1, v___f_1180_);
v___x_1212_ = l_Lean_ConstantInfo_name(v_val_1137_);
lean_dec_ref_known(v_val_1137_, 1);
v___x_1213_ = lean_environment_find(v_env_1207_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 1)
{
lean_object* v_val_1214_; 
v_val_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_val_1214_);
if (lean_obj_tag(v_val_1214_) == 2)
{
lean_object* v_toConstantVal_1215_; lean_object* v_val_1216_; lean_object* v_toConstantVal_1217_; lean_object* v_all_1218_; lean_object* v_name_1219_; lean_object* v_levelParams_1220_; lean_object* v_type_1221_; lean_object* v_all_1222_; lean_object* v_name_1223_; lean_object* v_levelParams_1224_; lean_object* v_type_1225_; uint8_t v___y_1227_; uint8_t v___x_1234_; 
lean_dec_ref_known(v___x_1213_, 1);
lean_dec_ref(v___f_1208_);
v_toConstantVal_1215_ = lean_ctor_get(v_val_1205_, 0);
v_val_1216_ = lean_ctor_get(v_val_1214_, 0);
lean_inc_ref(v_val_1216_);
lean_dec_ref_known(v_val_1214_, 1);
v_toConstantVal_1217_ = lean_ctor_get(v_val_1216_, 0);
lean_inc_ref(v_toConstantVal_1217_);
v_all_1218_ = lean_ctor_get(v_val_1205_, 2);
v_name_1219_ = lean_ctor_get(v_toConstantVal_1215_, 0);
v_levelParams_1220_ = lean_ctor_get(v_toConstantVal_1215_, 1);
v_type_1221_ = lean_ctor_get(v_toConstantVal_1215_, 2);
v_all_1222_ = lean_ctor_get(v_val_1216_, 2);
lean_inc(v_all_1222_);
lean_dec_ref(v_val_1216_);
v_name_1223_ = lean_ctor_get(v_toConstantVal_1217_, 0);
lean_inc(v_name_1223_);
v_levelParams_1224_ = lean_ctor_get(v_toConstantVal_1217_, 1);
lean_inc(v_levelParams_1224_);
v_type_1225_ = lean_ctor_get(v_toConstantVal_1217_, 2);
lean_inc_ref(v_type_1225_);
lean_dec_ref(v_toConstantVal_1217_);
v___x_1234_ = lean_name_eq(v_name_1219_, v_name_1223_);
lean_dec(v_name_1223_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v_type_1225_);
v___y_1227_ = v___x_1234_;
goto v___jp_1226_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_expr_eqv(v_type_1221_, v_type_1225_);
lean_dec_ref(v_type_1225_);
v___y_1227_ = v___x_1235_;
goto v___jp_1226_;
}
v___jp_1226_:
{
if (v___y_1227_ == 0)
{
lean_dec(v_levelParams_1224_);
lean_dec(v_all_1222_);
lean_del_object(v___x_1129_);
goto v___jp_1209_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_levelParams_1220_, v_levelParams_1224_);
lean_dec(v_levelParams_1224_);
if (v___x_1228_ == 0)
{
lean_dec(v_all_1222_);
lean_del_object(v___x_1129_);
goto v___jp_1209_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_all_1218_, v_all_1222_);
lean_dec(v_all_1222_);
if (v___x_1229_ == 0)
{
lean_del_object(v___x_1129_);
goto v___jp_1209_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
lean_dec_ref(v_val_1205_);
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1139_);
lean_dec(v_name_1122_);
v___x_1230_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1230_);
v___x_1232_ = v___x_1129_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_val_1214_);
lean_dec_ref(v_val_1205_);
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v___x_1236_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1208_, v___x_1213_, v_a_1123_, v_a_1124_);
lean_dec_ref_known(v___x_1213_, 1);
v___y_1165_ = v___x_1236_;
goto v___jp_1164_;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec_ref(v_val_1205_);
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v___x_1237_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1208_, v___x_1213_, v_a_1123_, v_a_1124_);
lean_dec(v___x_1213_);
v___y_1165_ = v___x_1237_;
goto v___jp_1164_;
}
v___jp_1209_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_1205_, v___f_1180_, v___x_1210_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1211_;
goto v___jp_1164_;
}
}
case 3:
{
lean_object* v_val_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1238_ = lean_ctor_get(v_val_1137_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_val_1137_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v_val_1137_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_val_1238_);
lean_dec(v_val_1137_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_val_1238_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1243_, v_a_1124_);
lean_dec_ref(v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v_a_1245_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1246_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1247_; 
v_a_1247_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1244_, 1);
v_a_1150_ = v_a_1247_;
goto v___jp_1149_;
}
}
}
}
case 4:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref_known(v_val_1137_, 1);
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3));
v___x_1251_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v___x_1250_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref_known(v___x_1251_, 1);
v___x_1252_ = lean_box(4);
v___x_1253_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1252_, v_a_1124_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v_a_1254_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1255_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1256_; 
v_a_1256_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1253_, 1);
v_a_1150_ = v_a_1256_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1257_; 
v_a_1257_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1251_, 1);
v_a_1150_ = v_a_1257_;
goto v___jp_1149_;
}
}
case 5:
{
lean_object* v_val_1258_; lean_object* v_toConstantVal_1259_; lean_object* v_numParams_1260_; lean_object* v_all_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1258_ = lean_ctor_get(v_val_1137_, 0);
lean_inc_ref(v_val_1258_);
lean_dec_ref_known(v_val_1137_, 1);
v_toConstantVal_1259_ = lean_ctor_get(v_val_1258_, 0);
lean_inc_ref(v_toConstantVal_1259_);
v_numParams_1260_ = lean_ctor_get(v_val_1258_, 1);
lean_inc(v_numParams_1260_);
v_all_1261_ = lean_ctor_get(v_val_1258_, 3);
lean_inc(v_all_1261_);
lean_dec_ref(v_val_1258_);
v___x_1262_ = lean_box(0);
v___x_1263_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_all_1261_, v___x_1262_, v_a_1123_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = lean_box(0);
v___x_1266_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_a_1264_, v___x_1265_, v_a_1124_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1266_, 1);
v___x_1267_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_a_1264_, v___x_1262_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_a_1268_, v___x_1265_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_levelParams_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref_known(v___x_1269_, 1);
v_levelParams_1270_ = lean_ctor_get(v_toConstantVal_1259_, 1);
lean_inc(v_levelParams_1270_);
lean_dec_ref(v_toConstantVal_1259_);
v___x_1271_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(v_a_1268_, v___x_1262_);
v___x_1272_ = 0;
v___x_1273_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1273_, 0, v_levelParams_1270_);
lean_ctor_set(v___x_1273_, 1, v_numParams_1260_);
lean_ctor_set(v___x_1273_, 2, v___x_1271_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*3, v___x_1272_);
v___x_1274_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1273_, v_a_1124_);
lean_dec_ref_known(v___x_1273_, 3);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v_a_1275_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1276_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1274_, 1);
v_a_1150_ = v_a_1277_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1278_; 
lean_dec(v_a_1268_);
lean_dec(v_numParams_1260_);
lean_dec_ref(v_toConstantVal_1259_);
v_a_1278_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1269_, 1);
v_a_1150_ = v_a_1278_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1279_; 
lean_dec(v_numParams_1260_);
lean_dec_ref(v_toConstantVal_1259_);
v_a_1279_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1267_, 1);
v_a_1150_ = v_a_1279_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1280_; 
lean_dec(v_a_1264_);
lean_dec(v_numParams_1260_);
lean_dec_ref(v_toConstantVal_1259_);
v_a_1280_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1266_, 1);
v_a_1150_ = v_a_1280_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1281_; 
lean_dec(v_numParams_1260_);
lean_dec_ref(v_toConstantVal_1259_);
v_a_1281_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1263_, 1);
v_a_1150_ = v_a_1281_;
goto v___jp_1149_;
}
}
case 6:
{
lean_object* v_val_1282_; lean_object* v___x_1283_; lean_object* v_toConstantVal_1284_; lean_object* v_env_1285_; lean_object* v_remaining_1286_; lean_object* v_pending_1287_; lean_object* v_postponedConstructors_1288_; lean_object* v_postponedRecursors_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1282_ = lean_ctor_get(v_val_1137_, 0);
lean_inc_ref(v_val_1282_);
lean_dec_ref_known(v_val_1137_, 1);
v___x_1283_ = lean_st_ref_take(v_a_1124_);
v_toConstantVal_1284_ = lean_ctor_get(v_val_1282_, 0);
lean_inc_ref(v_toConstantVal_1284_);
lean_dec_ref(v_val_1282_);
v_env_1285_ = lean_ctor_get(v___x_1283_, 0);
v_remaining_1286_ = lean_ctor_get(v___x_1283_, 1);
v_pending_1287_ = lean_ctor_get(v___x_1283_, 2);
v_postponedConstructors_1288_ = lean_ctor_get(v___x_1283_, 3);
v_postponedRecursors_1289_ = lean_ctor_get(v___x_1283_, 4);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1291_ = v___x_1283_;
v_isShared_1292_ = v_isSharedCheck_1301_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_postponedRecursors_1289_);
lean_inc(v_postponedConstructors_1288_);
lean_inc(v_pending_1287_);
lean_inc(v_remaining_1286_);
lean_inc(v_env_1285_);
lean_dec(v___x_1283_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1301_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_name_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v_name_1293_ = lean_ctor_get(v_toConstantVal_1284_, 0);
lean_inc(v_name_1293_);
lean_dec_ref(v_toConstantVal_1284_);
v___x_1294_ = l_Lean_NameSet_insert(v_postponedConstructors_1288_, v_name_1293_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 3, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_env_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_remaining_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_pending_1287_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v_postponedRecursors_1289_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_st_ref_set(v_a_1124_, v___x_1296_);
v___x_1298_ = lean_box(0);
v___x_1299_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v___x_1298_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1299_;
goto v___jp_1164_;
}
}
}
default: 
{
lean_object* v_val_1302_; lean_object* v___x_1303_; lean_object* v_toConstantVal_1304_; lean_object* v_env_1305_; lean_object* v_remaining_1306_; lean_object* v_pending_1307_; lean_object* v_postponedConstructors_1308_; lean_object* v_postponedRecursors_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___f_1180_);
lean_del_object(v___x_1129_);
v_val_1302_ = lean_ctor_get(v_val_1137_, 0);
lean_inc_ref(v_val_1302_);
lean_dec_ref_known(v_val_1137_, 1);
v___x_1303_ = lean_st_ref_take(v_a_1124_);
v_toConstantVal_1304_ = lean_ctor_get(v_val_1302_, 0);
lean_inc_ref(v_toConstantVal_1304_);
lean_dec_ref(v_val_1302_);
v_env_1305_ = lean_ctor_get(v___x_1303_, 0);
v_remaining_1306_ = lean_ctor_get(v___x_1303_, 1);
v_pending_1307_ = lean_ctor_get(v___x_1303_, 2);
v_postponedConstructors_1308_ = lean_ctor_get(v___x_1303_, 3);
v_postponedRecursors_1309_ = lean_ctor_get(v___x_1303_, 4);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1311_ = v___x_1303_;
v_isShared_1312_ = v_isSharedCheck_1321_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_postponedRecursors_1309_);
lean_inc(v_postponedConstructors_1308_);
lean_inc(v_pending_1307_);
lean_inc(v_remaining_1306_);
lean_inc(v_env_1305_);
lean_dec(v___x_1303_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1321_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_name_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v_name_1313_ = lean_ctor_get(v_toConstantVal_1304_, 0);
lean_inc(v_name_1313_);
lean_dec_ref(v_toConstantVal_1304_);
v___x_1314_ = l_Lean_NameSet_insert(v_postponedRecursors_1309_, v_name_1313_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_env_1305_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_remaining_1306_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_pending_1307_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_postponedConstructors_1308_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_st_ref_set(v_a_1124_, v___x_1316_);
v___x_1318_ = lean_box(0);
v___x_1319_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1122_, v___x_1318_, v_a_1123_, v_a_1124_);
v___y_1165_ = v___x_1319_;
goto v___jp_1164_;
}
}
}
}
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0));
v___x_1152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1122_, v___x_1148_);
v___x_1153_ = lean_string_append(v___x_1151_, v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1));
v___x_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_io_error_to_string(v_a_1150_);
v___x_1157_ = lean_string_append(v___x_1155_, v___x_1156_);
lean_dec_ref(v___x_1156_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 18);
lean_ctor_set(v___x_1139_, 0, v___x_1157_);
v___x_1159_ = v___x_1139_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1159_);
v___x_1161_ = v___x_1144_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
v___jp_1164_:
{
if (lean_obj_tag(v___y_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_del_object(v___x_1144_);
lean_del_object(v___x_1139_);
lean_dec(v_name_1122_);
v_a_1166_ = lean_ctor_get(v___y_1165_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___y_1165_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1168_ = v___y_1165_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___y_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_a_1170_; lean_object* v___x_1172_; 
v_a_1170_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_a_1170_);
lean_dec(v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_a_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___y_1165_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___y_1165_, 1);
v_a_1150_ = v_a_1175_;
goto v___jp_1149_;
}
}
}
}
else
{
lean_del_object(v___x_1139_);
lean_dec(v_val_1137_);
lean_del_object(v___x_1129_);
lean_dec(v_name_1122_);
return v___x_1142_;
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec(v___x_1136_);
lean_del_object(v___x_1129_);
lean_dec(v_name_1122_);
v___x_1325_ = lean_obj_once(&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7, &l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7_once, _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7);
v___x_1326_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v___x_1325_, v_a_1123_, v_a_1124_);
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_name_1122_);
v_a_1328_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1126_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1126_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(lean_object* v_init_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
lean_object* v_k_1341_; lean_object* v_l_1342_; lean_object* v_r_1343_; lean_object* v___x_1344_; 
v_k_1341_ = lean_ctor_get(v_x_1337_, 1);
lean_inc(v_k_1341_);
v_l_1342_ = lean_ctor_get(v_x_1337_, 3);
lean_inc(v_l_1342_);
v_r_1343_ = lean_ctor_get(v_x_1337_, 4);
lean_inc(v_r_1343_);
lean_dec_ref_known(v_x_1337_, 5);
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v_init_1336_, v_l_1342_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; 
lean_dec_ref_known(v___x_1344_, 1);
v___x_1345_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_k_1341_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref_known(v___x_1345_, 1);
v___x_1346_ = lean_box(0);
v_init_1336_ = v___x_1346_;
v_x_1337_ = v_r_1343_;
goto _start;
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v_r_1343_);
v_a_1348_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1345_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_dec(v_r_1343_);
lean_dec(v_k_1341_);
return v___x_1344_;
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_init_1336_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(lean_object* v_names_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v___x_1362_, v_names_1358_, v_a_1359_, v_a_1360_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1371_);
v___x_1365_ = v___x_1363_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v___x_1363_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1362_);
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1362_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants___boxed(lean_object* v_names_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v_names_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object* v_as_x27_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_1385_, v_b_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v_as_x27_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg___boxed(lean_object* v_as_x27_1391_, lean_object* v_b_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1391_, v_b_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v_as_x27_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12___boxed(lean_object* v_init_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v_init_1397_, v_x_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___boxed(lean_object* v_name_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_name_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v_x_1408_, v_x_1409_, v___y_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___boxed(lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(v_x_1414_, v_x_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(lean_object* v_00_u03b2_1420_, lean_object* v_m_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v_m_1421_, v_a_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___boxed(lean_object* v_00_u03b2_1424_, lean_object* v_m_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(v_00_u03b2_1424_, v_m_1425_, v_a_1426_);
lean_dec(v_a_1426_);
lean_dec_ref(v_m_1425_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(lean_object* v_as_1428_, lean_object* v_as_x27_1429_, lean_object* v_b_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v_as_x27_1429_, v_b_1430_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___boxed(lean_object* v_as_1436_, lean_object* v_as_x27_1437_, lean_object* v_b_1438_, lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(v_as_1436_, v_as_x27_1437_, v_b_1438_, v_a_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v_as_x27_1437_);
lean_dec(v_as_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(lean_object* v_as_1444_, lean_object* v_as_x27_1445_, lean_object* v_b_1446_, lean_object* v_a_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___redArg(v_as_x27_1445_, v_b_1446_, v___y_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___boxed(lean_object* v_as_1452_, lean_object* v_as_x27_1453_, lean_object* v_b_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(v_as_1452_, v_as_x27_1453_, v_b_1454_, v_a_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v_as_x27_1453_);
lean_dec(v_as_1452_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(lean_object* v_as_1460_, lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v_a_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1461_, v_b_1462_, v___y_1464_, v___y_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___boxed(lean_object* v_as_1468_, lean_object* v_as_x27_1469_, lean_object* v_b_1470_, lean_object* v_a_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(v_as_1468_, v_as_x27_1469_, v_b_1470_, v_a_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v_as_x27_1469_);
lean_dec(v_as_1468_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___redArg(v_a_1477_, v_x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_a_1481_, lean_object* v_x_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3_spec__4(v_00_u03b2_1480_, v_a_1481_, v_x_1482_);
lean_dec(v_x_1482_);
lean_dec(v_a_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(lean_object* v_init_1486_, lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
if (lean_obj_tag(v_x_1487_) == 0)
{
lean_object* v_k_1491_; lean_object* v_l_1492_; lean_object* v_r_1493_; lean_object* v___x_1501_; 
v_k_1491_ = lean_ctor_get(v_x_1487_, 1);
lean_inc(v_k_1491_);
v_l_1492_ = lean_ctor_get(v_x_1487_, 3);
lean_inc(v_l_1492_);
v_r_1493_ = lean_ctor_get(v_x_1487_, 4);
lean_inc(v_r_1493_);
lean_dec_ref_known(v_x_1487_, 5);
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1486_, v_l_1492_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v___x_1501_, 0);
lean_dec(v_unused_1525_);
v___x_1503_ = v___x_1501_;
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v___x_1501_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1524_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v_env_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_st_ref_get(v___y_1489_);
v_env_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc_ref(v_env_1506_);
lean_dec(v___x_1505_);
lean_inc(v_k_1491_);
v___x_1507_ = lean_environment_find(v_env_1506_, v_k_1491_);
if (lean_obj_tag(v___x_1507_) == 1)
{
lean_object* v_val_1508_; 
v_val_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v___x_1507_, 1);
if (lean_obj_tag(v_val_1508_) == 6)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v_val_1508_, 0);
lean_inc_ref(v_val_1509_);
lean_dec_ref_known(v_val_1508_, 1);
v___x_1510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v___y_1488_, v_k_1491_);
if (lean_obj_tag(v___x_1510_) == 1)
{
lean_object* v_val_1511_; 
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1510_, 1);
if (lean_obj_tag(v_val_1511_) == 6)
{
lean_object* v_val_1512_; uint8_t v___x_1513_; 
v_val_1512_ = lean_ctor_get(v_val_1511_, 0);
lean_inc_ref(v_val_1512_);
lean_dec_ref_known(v_val_1511_, 1);
v___x_1513_ = l_Lean_instBEqConstructorVal_beq(v_val_1509_, v_val_1512_);
lean_dec_ref(v_val_1512_);
lean_dec_ref(v_val_1509_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v_r_1493_);
v___x_1514_ = 1;
v___x_1515_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1));
v___x_1516_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1491_, v___x_1514_);
v___x_1517_ = lean_string_append(v___x_1515_, v___x_1516_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = lean_mk_io_user_error(v___x_1517_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
lean_ctor_set(v___x_1503_, 0, v___x_1518_);
v___x_1520_ = v___x_1503_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
else
{
lean_object* v___x_1522_; 
lean_del_object(v___x_1503_);
lean_dec(v_k_1491_);
v___x_1522_ = lean_box(0);
v_init_1486_ = v___x_1522_;
v_x_1487_ = v_r_1493_;
goto _start;
}
}
else
{
lean_dec(v_val_1511_);
lean_dec_ref(v_val_1509_);
lean_del_object(v___x_1503_);
lean_dec(v_r_1493_);
goto v___jp_1494_;
}
}
else
{
lean_dec(v___x_1510_);
lean_dec_ref(v_val_1509_);
lean_del_object(v___x_1503_);
lean_dec(v_r_1493_);
goto v___jp_1494_;
}
}
else
{
lean_dec(v_val_1508_);
lean_del_object(v___x_1503_);
lean_dec(v_r_1493_);
goto v___jp_1494_;
}
}
else
{
lean_dec(v___x_1507_);
lean_del_object(v___x_1503_);
lean_dec(v_r_1493_);
goto v___jp_1494_;
}
}
}
else
{
lean_dec(v_r_1493_);
lean_dec(v_k_1491_);
return v___x_1501_;
}
v___jp_1494_:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0));
v___x_1496_ = 1;
v___x_1497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1491_, v___x_1496_);
v___x_1498_ = lean_string_append(v___x_1495_, v___x_1497_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = lean_mk_io_user_error(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_init_1486_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object* v_init_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1528_, v_x_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_postponedConstructors_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = lean_st_ref_get(v_a_1535_);
v_postponedConstructors_1538_ = lean_ctor_get(v___x_1537_, 3);
lean_inc(v_postponedConstructors_1538_);
lean_dec(v___x_1537_);
v___x_1539_ = lean_box(0);
v___x_1540_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v___x_1539_, v_postponedConstructors_1538_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1540_, 0);
lean_dec(v_unused_1548_);
v___x_1542_ = v___x_1540_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v___x_1540_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1539_);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1539_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1540_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors___boxed(lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_a_1557_, v_a_1558_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(lean_object* v_init_1563_, lean_object* v_x_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v_k_1568_; lean_object* v_l_1569_; lean_object* v_r_1570_; lean_object* v___x_1578_; 
v_k_1568_ = lean_ctor_get(v_x_1564_, 1);
lean_inc(v_k_1568_);
v_l_1569_ = lean_ctor_get(v_x_1564_, 3);
lean_inc(v_l_1569_);
v_r_1570_ = lean_ctor_get(v_x_1564_, 4);
lean_inc(v_r_1570_);
lean_dec_ref_known(v_x_1564_, 5);
v___x_1578_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1563_, v_l_1569_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1601_; 
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1602_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v_env_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_st_ref_get(v___y_1566_);
v_env_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc_ref(v_env_1583_);
lean_dec(v___x_1582_);
lean_inc(v_k_1568_);
v___x_1584_ = lean_environment_find(v_env_1583_, v_k_1568_);
if (lean_obj_tag(v___x_1584_) == 1)
{
lean_object* v_val_1585_; 
v_val_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v___x_1584_, 1);
if (lean_obj_tag(v_val_1585_) == 7)
{
lean_object* v_val_1586_; lean_object* v___x_1587_; 
v_val_1586_ = lean_ctor_get(v_val_1585_, 0);
lean_inc_ref(v_val_1586_);
lean_dec_ref_known(v_val_1585_, 1);
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___redArg(v___y_1565_, v_k_1568_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
if (lean_obj_tag(v_val_1588_) == 7)
{
lean_object* v_val_1589_; uint8_t v___x_1590_; 
v_val_1589_ = lean_ctor_get(v_val_1588_, 0);
lean_inc_ref(v_val_1589_);
lean_dec_ref_known(v_val_1588_, 1);
v___x_1590_ = l_Lean_instBEqRecursorVal_beq(v_val_1586_, v_val_1589_);
lean_dec_ref(v_val_1589_);
lean_dec_ref(v_val_1586_);
if (v___x_1590_ == 0)
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec(v_r_1570_);
v___x_1591_ = 1;
v___x_1592_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1));
v___x_1593_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1568_, v___x_1591_);
v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = lean_mk_io_user_error(v___x_1594_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set_tag(v___x_1580_, 1);
lean_ctor_set(v___x_1580_, 0, v___x_1595_);
v___x_1597_ = v___x_1580_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
lean_object* v___x_1599_; 
lean_del_object(v___x_1580_);
lean_dec(v_k_1568_);
v___x_1599_ = lean_box(0);
v_init_1563_ = v___x_1599_;
v_x_1564_ = v_r_1570_;
goto _start;
}
}
else
{
lean_dec(v_val_1588_);
lean_dec_ref(v_val_1586_);
lean_del_object(v___x_1580_);
lean_dec(v_r_1570_);
goto v___jp_1571_;
}
}
else
{
lean_dec(v___x_1587_);
lean_dec_ref(v_val_1586_);
lean_del_object(v___x_1580_);
lean_dec(v_r_1570_);
goto v___jp_1571_;
}
}
else
{
lean_dec(v_val_1585_);
lean_del_object(v___x_1580_);
lean_dec(v_r_1570_);
goto v___jp_1571_;
}
}
else
{
lean_dec(v___x_1584_);
lean_del_object(v___x_1580_);
lean_dec(v_r_1570_);
goto v___jp_1571_;
}
}
}
else
{
lean_dec(v_r_1570_);
lean_dec(v_k_1568_);
return v___x_1578_;
}
v___jp_1571_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1572_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0));
v___x_1573_ = 1;
v___x_1574_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1568_, v___x_1573_);
v___x_1575_ = lean_string_append(v___x_1572_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = lean_mk_io_user_error(v___x_1575_);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_init_1563_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object* v_init_1605_, lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1605_, v_x_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_postponedRecursors_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1614_ = lean_st_ref_get(v_a_1612_);
v_postponedRecursors_1615_ = lean_ctor_get(v___x_1614_, 4);
lean_inc(v_postponedRecursors_1615_);
lean_dec(v___x_1614_);
v___x_1616_ = lean_box(0);
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v___x_1616_, v_postponedRecursors_1615_, v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v___x_1617_, 0);
lean_dec(v_unused_1625_);
v___x_1619_ = v___x_1617_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v___x_1617_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1616_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1617_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1617_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors___boxed(lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
lean_inc(v_x_1638_);
return v_x_1638_;
}
else
{
lean_object* v_key_1640_; lean_object* v_value_1641_; lean_object* v_tail_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_key_1640_ = lean_ctor_get(v_x_1639_, 0);
v_value_1641_ = lean_ctor_get(v_x_1639_, 1);
v_tail_1642_ = lean_ctor_get(v_x_1639_, 2);
v___x_1643_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1638_, v_tail_1642_);
lean_inc(v_value_1641_);
lean_inc(v_key_1640_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_key_1640_);
lean_ctor_set(v___x_1644_, 1, v_value_1641_);
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1643_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1___boxed(lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec(v_x_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(lean_object* v_as_1649_, size_t v_i_1650_, size_t v_stop_1651_, lean_object* v_b_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_usize_dec_eq(v_i_1650_, v_stop_1651_);
if (v___x_1653_ == 0)
{
size_t v___x_1654_; size_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_sub(v_i_1650_, v___x_1654_);
v___x_1656_ = lean_array_uget_borrowed(v_as_1649_, v___x_1655_);
v___x_1657_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_b_1652_, v___x_1656_);
lean_dec(v_b_1652_);
v_i_1650_ = v___x_1655_;
v_b_1652_ = v___x_1657_;
goto _start;
}
else
{
return v_b_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2___boxed(lean_object* v_as_1659_, lean_object* v_i_1660_, lean_object* v_stop_1661_, lean_object* v_b_1662_){
_start:
{
size_t v_i_boxed_1663_; size_t v_stop_boxed_1664_; lean_object* v_res_1665_; 
v_i_boxed_1663_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_stop_boxed_1664_ = lean_unbox_usize(v_stop_1661_);
lean_dec(v_stop_1661_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_as_1659_, v_i_boxed_1663_, v_stop_boxed_1664_, v_b_1662_);
lean_dec_ref(v_as_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(lean_object* v_as_x27_1666_, lean_object* v_b_1667_){
_start:
{
if (lean_obj_tag(v_as_x27_1666_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v_b_1667_);
return v___x_1669_;
}
else
{
lean_object* v_head_1670_; lean_object* v_tail_1671_; lean_object* v_fst_1672_; lean_object* v_snd_1673_; uint8_t v___x_1674_; 
v_head_1670_ = lean_ctor_get(v_as_x27_1666_, 0);
v_tail_1671_ = lean_ctor_get(v_as_x27_1666_, 1);
v_fst_1672_ = lean_ctor_get(v_head_1670_, 0);
v_snd_1673_ = lean_ctor_get(v_head_1670_, 1);
v___x_1674_ = l_Lean_ConstantInfo_isUnsafe(v_snd_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Lean_ConstantInfo_isPartial(v_snd_1673_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_inc(v_fst_1672_);
v___x_1676_ = l_Lean_NameSet_insert(v_b_1667_, v_fst_1672_);
v_as_x27_1666_ = v_tail_1671_;
v_b_1667_ = v___x_1676_;
goto _start;
}
else
{
v_as_x27_1666_ = v_tail_1671_;
goto _start;
}
}
else
{
v_as_x27_1666_ = v_tail_1671_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___boxed(lean_object* v_as_x27_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1680_, v_b_1681_);
lean_dec(v_as_x27_1680_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay(lean_object* v_newConstants_1684_, lean_object* v_env_1685_){
_start:
{
lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v_buckets_1708_; lean_object* v_remaining_1709_; lean_object* v___y_1711_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_buckets_1708_ = lean_ctor_get(v_newConstants_1684_, 1);
v_remaining_1709_ = l_Lean_NameSet_empty;
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_array_get_size(v_buckets_1708_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_nat_dec_lt(v___x_1730_, v___x_1729_);
if (v___x_1731_ == 0)
{
v___y_1711_ = v___x_1728_;
goto v___jp_1710_;
}
else
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_usize_of_nat(v___x_1729_);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_1708_, v___x_1732_, v___x_1733_, v___x_1728_);
v___y_1711_ = v___x_1734_;
goto v___jp_1710_;
}
v___jp_1687_:
{
if (lean_obj_tag(v___y_1689_) == 0)
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1698_; 
v_isSharedCheck_1698_ = !lean_is_exclusive(v___y_1689_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v___y_1689_, 0);
lean_dec(v_unused_1699_);
v___x_1691_ = v___y_1689_;
v_isShared_1692_ = v_isSharedCheck_1698_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v___y_1689_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1698_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v_env_1694_; lean_object* v___x_1696_; 
v___x_1693_ = lean_st_ref_get(v___y_1688_);
lean_dec(v___y_1688_);
v_env_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc_ref(v_env_1694_);
lean_dec(v___x_1693_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_env_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_env_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v___y_1688_);
v_a_1700_ = lean_ctor_get(v___y_1689_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___y_1689_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___y_1689_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___y_1689_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
v___jp_1710_:
{
lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1712_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v___y_1711_, v_remaining_1709_);
lean_dec(v___y_1711_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc_n(v_a_1713_, 2);
lean_dec_ref(v___x_1712_);
v___x_1714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1714_, 0, v_env_1685_);
lean_ctor_set(v___x_1714_, 1, v_a_1713_);
lean_ctor_set(v___x_1714_, 2, v_remaining_1709_);
lean_ctor_set(v___x_1714_, 3, v_remaining_1709_);
lean_ctor_set(v___x_1714_, 4, v_remaining_1709_);
v___x_1715_ = lean_st_mk_ref(v___x_1714_);
v___x_1716_ = lean_box(0);
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__12(v___x_1716_, v_a_1713_, v_newConstants_1684_, v___x_1715_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1718_; 
lean_dec_ref_known(v___x_1717_, 1);
v___x_1718_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_newConstants_1684_, v___x_1715_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref_known(v___x_1718_, 1);
v___x_1719_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_newConstants_1684_, v___x_1715_);
v___y_1688_ = v___x_1715_;
v___y_1689_ = v___x_1719_;
goto v___jp_1687_;
}
else
{
v___y_1688_ = v___x_1715_;
v___y_1689_ = v___x_1718_;
goto v___jp_1687_;
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v___x_1715_);
v_a_1720_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1717_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1717_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay___boxed(lean_object* v_newConstants_1735_, lean_object* v_env_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Kernel_Environment_replay(v_newConstants_1735_, v_env_1736_);
lean_dec_ref(v_newConstants_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(lean_object* v_as_1739_, lean_object* v_as_x27_1740_, lean_object* v_b_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1740_, v_b_1741_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___boxed(lean_object* v_as_1745_, lean_object* v_as_x27_1746_, lean_object* v_b_1747_, lean_object* v_a_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(v_as_1745_, v_as_x27_1746_, v_b_1747_, v_a_1748_);
lean_dec(v_as_x27_1746_);
lean_dec(v_as_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object* v_newConstants_1751_, lean_object* v_env_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_elab_environment_to_kernel_env(v_env_1752_);
v___x_1755_ = l_Lean_Kernel_Environment_replay(v_newConstants_1751_, v___x_1754_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_elab_environment_of_kernel_env(v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1755_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1755_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay___boxed(lean_object* v_newConstants_1773_, lean_object* v_env_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Environment_replay(v_newConstants_1773_, v_env_1774_);
lean_dec_ref(v_newConstants_1773_);
return v_res_1776_;
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
