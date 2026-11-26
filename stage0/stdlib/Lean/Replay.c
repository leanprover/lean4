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
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_instBEqConstantInfo_beq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "', listed in the `all` field of '"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__1_value;
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "', is not a stored inductive type"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__11(lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "', listed as a constructor of '"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "', is not a stored constructor"};
static const lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Invalid inductive type "};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':\n"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value;
static const lean_ctor_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inductive type '"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "' is not listed in its own `all` field"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__8 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__8_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Replay.0.Lean.Kernel.Environment.Replay.replayConstant"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7_value;
static const lean_string_object l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Replay"};
static const lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6 = (const lean_object*)&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6_value;
static lean_once_cell_t l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration '"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "' is stored under the name '"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_Environment_replay___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__0 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__0_value;
static const lean_string_object l_Lean_Kernel_Environment_replay___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__1 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__1_value;
static const lean_ctor_object l_Lean_Kernel_Environment_replay___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_replay___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Kernel_Environment_replay___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_replay___closed__2_value_aux_0),((lean_object*)&l_Lean_Kernel_Environment_replay___closed__1_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__2 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__2_value;
static const lean_string_object l_Lean_Kernel_Environment_replay___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__3 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__3_value;
static const lean_string_object l_Lean_Kernel_Environment_replay___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__4 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__4_value;
static const lean_ctor_object l_Lean_Kernel_Environment_replay___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_replay___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Kernel_Environment_replay___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_replay___closed__5_value_aux_0),((lean_object*)&l_Lean_Kernel_Environment_replay___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Kernel_Environment_replay___closed__5 = (const lean_object*)&l_Lean_Kernel_Environment_replay___closed__5_value;
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
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_745_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
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
v___x_759_ = v_reuseFailAlloc_764_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_st_ref_put(v_a_736_, v___x_759_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_762_ = v___x_747_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
if (lean_obj_tag(v_x_783_) == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
else
{
if (lean_obj_tag(v_x_783_) == 0)
{
uint8_t v___x_786_; 
v___x_786_ = 0;
return v___x_786_;
}
else
{
lean_object* v_val_787_; lean_object* v_val_788_; uint8_t v___x_789_; 
v_val_787_ = lean_ctor_get(v_x_782_, 0);
v_val_788_ = lean_ctor_get(v_x_783_, 0);
v___x_789_ = l_Lean_instBEqConstantInfo_beq(v_val_787_, v_val_788_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6___boxed(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(v_x_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec(v_x_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0(void){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_instMonadEIO___redArg();
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13(lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___x_38273__overap_804_; lean_object* v___x_805_; 
v___x_799_ = lean_obj_once(&l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0, &l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0_once, _init_l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___closed__0);
v___x_800_ = l_StateRefT_x27_instMonad___redArg(v___x_799_);
v___x_801_ = lean_box(0);
v___x_802_ = l_instInhabitedOfMonad___redArg(v___x_800_, v___x_801_);
v___f_803_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_803_, 0, v___x_802_);
v___x_38273__overap_804_ = lean_panic_fn_borrowed(v___f_803_, v_msg_795_);
lean_dec_ref(v___f_803_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
v___x_805_ = lean_apply_3(v___x_38273__overap_804_, v___y_796_, v___y_797_, lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13___boxed(lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13(v_msg_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(lean_object* v_name_813_, lean_object* v_____r_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_env_819_; lean_object* v_remaining_820_; lean_object* v_pending_821_; lean_object* v_postponedConstructors_822_; lean_object* v_postponedRecursors_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_834_; 
v___x_818_ = lean_st_ref_take(v___y_816_);
v_env_819_ = lean_ctor_get(v___x_818_, 0);
v_remaining_820_ = lean_ctor_get(v___x_818_, 1);
v_pending_821_ = lean_ctor_get(v___x_818_, 2);
v_postponedConstructors_822_ = lean_ctor_get(v___x_818_, 3);
v_postponedRecursors_823_ = lean_ctor_get(v___x_818_, 4);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_834_ == 0)
{
v___x_825_ = v___x_818_;
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_postponedRecursors_823_);
lean_inc(v_postponedConstructors_822_);
lean_inc(v_pending_821_);
lean_inc(v_remaining_820_);
lean_inc(v_env_819_);
lean_dec(v___x_818_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_834_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_813_, v_pending_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 2, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_env_819_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_remaining_820_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_postponedConstructors_822_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_postponedRecursors_823_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_st_ref_put(v___y_816_, v___x_829_);
v___x_831_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___closed__0));
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed(lean_object* v_name_835_, lean_object* v_____r_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_835_, v_____r_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v_name_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(lean_object* v_val_841_, lean_object* v___f_842_, lean_object* v_____r_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_847_, 0, v_val_841_);
v___x_848_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_847_, v___y_845_);
lean_dec_ref_known(v___x_847_, 1);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
v___x_850_ = lean_apply_4(v___f_842_, v_a_849_, v___y_844_, v___y_845_, lean_box(0));
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___f_842_);
v_a_851_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_848_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_848_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed(lean_object* v_val_859_, lean_object* v___f_860_, lean_object* v_____r_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_859_, v___f_860_, v_____r_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(lean_object* v___f_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
v___x_872_ = lean_apply_4(v___f_866_, v___x_871_, v___y_868_, v___y_869_, lean_box(0));
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2___boxed(lean_object* v___f_873_, lean_object* v_x_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_873_, v_x_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v_x_874_);
return v_res_878_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object* v_a_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = 0;
return v___x_881_;
}
else
{
lean_object* v_head_882_; lean_object* v_tail_883_; uint8_t v___x_884_; 
v_head_882_ = lean_ctor_get(v_x_880_, 0);
v_tail_883_ = lean_ctor_get(v_x_880_, 1);
v___x_884_ = lean_name_eq(v_a_879_, v_head_882_);
if (v___x_884_ == 0)
{
v_x_880_ = v_tail_883_;
goto _start;
}
else
{
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec(v_a_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v___x_892_; 
v___x_892_ = lean_box(0);
return v___x_892_;
}
else
{
lean_object* v_key_893_; lean_object* v_value_894_; lean_object* v_tail_895_; uint8_t v___x_896_; 
v_key_893_ = lean_ctor_get(v_x_891_, 0);
v_value_894_ = lean_ctor_get(v_x_891_, 1);
v_tail_895_ = lean_ctor_get(v_x_891_, 2);
v___x_896_ = lean_name_eq(v_key_893_, v_a_890_);
if (v___x_896_ == 0)
{
v_x_891_ = v_tail_895_;
goto _start;
}
else
{
lean_object* v___x_898_; 
lean_inc(v_value_894_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_value_894_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object* v_a_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg(v_a_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec(v_a_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_buckets_904_; lean_object* v___x_905_; uint64_t v___y_907_; 
v_buckets_904_ = lean_ctor_get(v_m_902_, 1);
v___x_905_ = lean_array_get_size(v_buckets_904_);
if (lean_obj_tag(v_a_903_) == 0)
{
uint64_t v___x_921_; 
v___x_921_ = 1723ULL;
v___y_907_ = v___x_921_;
goto v___jp_906_;
}
else
{
uint64_t v_hash_922_; 
v_hash_922_ = lean_ctor_get_uint64(v_a_903_, sizeof(void*)*2);
v___y_907_ = v_hash_922_;
goto v___jp_906_;
}
v___jp_906_:
{
uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v_fold_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_908_ = 32ULL;
v___x_909_ = lean_uint64_shift_right(v___y_907_, v___x_908_);
v_fold_910_ = lean_uint64_xor(v___y_907_, v___x_909_);
v___x_911_ = 16ULL;
v___x_912_ = lean_uint64_shift_right(v_fold_910_, v___x_911_);
v___x_913_ = lean_uint64_xor(v_fold_910_, v___x_912_);
v___x_914_ = lean_uint64_to_usize(v___x_913_);
v___x_915_ = lean_usize_of_nat(v___x_905_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_sub(v___x_915_, v___x_916_);
v___x_918_ = lean_usize_land(v___x_914_, v___x_917_);
v___x_919_ = lean_array_uget_borrowed(v_buckets_904_, v___x_918_);
v___x_920_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg(v_a_903_, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg___boxed(lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v_m_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_m_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(uint8_t v___x_929_, lean_object* v_name_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v___y_933_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_name_930_);
v___x_935_ = l_List_reverse___redArg(v_x_932_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
else
{
lean_object* v_head_937_; lean_object* v_tail_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_961_; 
v_head_937_ = lean_ctor_get(v_x_931_, 0);
v_tail_938_ = lean_ctor_get(v_x_931_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_961_ == 0)
{
v___x_940_ = v_x_931_;
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_tail_938_);
lean_inc(v_head_937_);
lean_dec(v_x_931_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v___y_933_, v_head_937_);
if (lean_obj_tag(v___x_954_) == 1)
{
lean_object* v_val_955_; 
v_val_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v___x_954_, 1);
if (lean_obj_tag(v_val_955_) == 5)
{
lean_object* v_val_956_; lean_object* v___x_958_; 
lean_dec(v_head_937_);
v_val_956_ = lean_ctor_get(v_val_955_, 0);
lean_inc_ref(v_val_956_);
lean_dec_ref_known(v_val_955_, 1);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_x_932_);
lean_ctor_set(v___x_940_, 0, v_val_956_);
v___x_958_ = v___x_940_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_val_956_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_x_932_);
v___x_958_ = v_reuseFailAlloc_960_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_x_931_ = v_tail_938_;
v_x_932_ = v___x_958_;
goto _start;
}
}
else
{
lean_dec(v_val_955_);
lean_del_object(v___x_940_);
lean_dec(v_tail_938_);
lean_dec(v_x_932_);
goto v___jp_942_;
}
}
else
{
lean_dec(v___x_954_);
lean_del_object(v___x_940_);
lean_dec(v_tail_938_);
lean_dec(v_x_932_);
goto v___jp_942_;
}
v___jp_942_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_943_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0));
v___x_944_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_937_, v___x_929_);
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
lean_dec_ref(v___x_944_);
v___x_946_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__1));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___x_948_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_930_, v___x_929_);
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
lean_dec_ref(v___x_948_);
v___x_950_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__2));
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
v___x_952_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object* v___x_962_, lean_object* v_name_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
uint8_t v___x_39454__boxed_968_; lean_object* v_res_969_; 
v___x_39454__boxed_968_ = lean_unbox(v___x_962_);
v_res_969_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v___x_39454__boxed_968_, v_name_963_, v_x_964_, v_x_965_, v___y_966_);
lean_dec_ref(v___y_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
if (lean_obj_tag(v_a_970_) == 0)
{
lean_object* v___x_972_; 
v___x_972_ = l_List_reverse___redArg(v_a_971_);
return v___x_972_;
}
else
{
lean_object* v_head_973_; lean_object* v_tail_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_985_; 
v_head_973_ = lean_ctor_get(v_a_970_, 0);
v_tail_974_ = lean_ctor_get(v_a_970_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_a_970_);
if (v_isSharedCheck_985_ == 0)
{
v___x_976_ = v_a_970_;
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_tail_974_);
lean_inc(v_head_973_);
lean_dec(v_a_970_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_985_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_978_ = l_Lean_ConstantInfo_name(v_head_973_);
v___x_979_ = l_Lean_ConstantInfo_type(v_head_973_);
lean_dec(v_head_973_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_a_971_);
lean_ctor_set(v___x_976_, 0, v___x_980_);
v___x_982_ = v___x_976_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_a_971_);
v___x_982_ = v_reuseFailAlloc_984_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
v_a_970_ = v_tail_974_;
v_a_971_ = v___x_982_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__11(lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
if (lean_obj_tag(v_a_986_) == 0)
{
lean_object* v___x_988_; 
v___x_988_ = l_List_reverse___redArg(v_a_987_);
return v___x_988_;
}
else
{
lean_object* v_head_989_; lean_object* v_fst_990_; lean_object* v_toConstantVal_991_; lean_object* v_tail_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1013_; 
v_head_989_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_head_989_);
v_fst_990_ = lean_ctor_get(v_head_989_, 0);
v_toConstantVal_991_ = lean_ctor_get(v_fst_990_, 0);
lean_inc_ref(v_toConstantVal_991_);
v_tail_992_ = lean_ctor_get(v_a_986_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_986_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_a_986_, 0);
lean_dec(v_unused_1014_);
v___x_994_ = v_a_986_;
v_isShared_995_ = v_isSharedCheck_1013_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_tail_992_);
lean_dec(v_a_986_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1013_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_snd_996_; lean_object* v_name_997_; lean_object* v_type_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_snd_996_ = lean_ctor_get(v_head_989_, 1);
lean_inc(v_snd_996_);
lean_dec(v_head_989_);
v_name_997_ = lean_ctor_get(v_toConstantVal_991_, 0);
v_type_998_ = lean_ctor_get(v_toConstantVal_991_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_toConstantVal_991_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_toConstantVal_991_, 1);
lean_dec(v_unused_1012_);
v___x_1000_ = v_toConstantVal_991_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_type_998_);
lean_inc(v_name_997_);
lean_dec(v_toConstantVal_991_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = lean_box(0);
v___x_1003_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__0(v_snd_996_, v___x_1002_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 2, v___x_1003_);
lean_ctor_set(v___x_1000_, 1, v_type_998_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_name_997_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_type_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_a_987_);
lean_ctor_set(v___x_994_, 0, v___x_1005_);
v___x_1007_ = v___x_994_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_a_987_);
v___x_1007_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
v_a_986_ = v_tail_992_;
v_a_987_ = v___x_1007_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(uint8_t v___x_1017_, lean_object* v_val_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref(v_val_1018_);
v___x_1023_ = l_List_reverse___redArg(v_x_1020_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
else
{
lean_object* v_head_1025_; lean_object* v_tail_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1050_; 
v_head_1025_ = lean_ctor_get(v_x_1019_, 0);
v_tail_1026_ = lean_ctor_get(v_x_1019_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1028_ = v_x_1019_;
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_tail_1026_);
lean_inc(v_head_1025_);
lean_dec(v_x_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1050_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v___y_1021_, v_head_1025_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; 
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1044_, 1);
if (lean_obj_tag(v_val_1045_) == 6)
{
lean_object* v___x_1047_; 
lean_dec(v_head_1025_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v_x_1020_);
lean_ctor_set(v___x_1028_, 0, v_val_1045_);
v___x_1047_ = v___x_1028_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_val_1045_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_x_1020_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v_x_1019_ = v_tail_1026_;
v_x_1020_ = v___x_1047_;
goto _start;
}
}
else
{
lean_dec(v_val_1045_);
lean_del_object(v___x_1028_);
lean_dec(v_tail_1026_);
lean_dec(v_x_1020_);
goto v___jp_1030_;
}
}
else
{
lean_dec(v___x_1044_);
lean_del_object(v___x_1028_);
lean_dec(v_tail_1026_);
lean_dec(v_x_1020_);
goto v___jp_1030_;
}
v___jp_1030_:
{
lean_object* v_toConstantVal_1031_; lean_object* v_name_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_toConstantVal_1031_ = lean_ctor_get(v_val_1018_, 0);
lean_inc_ref(v_toConstantVal_1031_);
lean_dec_ref(v_val_1018_);
v_name_1032_ = lean_ctor_get(v_toConstantVal_1031_, 0);
lean_inc(v_name_1032_);
lean_dec_ref(v_toConstantVal_1031_);
v___x_1033_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0));
v___x_1034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1025_, v___x_1017_);
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__0));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1032_, v___x_1017_);
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___closed__1));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg___boxed(lean_object* v___x_1051_, lean_object* v_val_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_39615__boxed_1057_; lean_object* v_res_1058_; 
v___x_39615__boxed_1057_ = lean_unbox(v___x_1051_);
v_res_1058_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v___x_39615__boxed_1057_, v_val_1052_, v_x_1053_, v_x_1054_, v___y_1055_);
lean_dec_ref(v___y_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(uint8_t v___x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = l_List_reverse___redArg(v_x_1061_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1089_; 
v_head_1067_ = lean_ctor_get(v_x_1060_, 0);
v_tail_1068_ = lean_ctor_get(v_x_1060_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1070_ = v_x_1060_;
v_isShared_1071_ = v_isSharedCheck_1089_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_tail_1068_);
lean_inc(v_head_1067_);
lean_dec(v_x_1060_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1089_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_ctors_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_ctors_1072_ = lean_ctor_get(v_head_1067_, 4);
v___x_1073_ = lean_box(0);
lean_inc(v_ctors_1072_);
lean_inc(v_head_1067_);
v___x_1074_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v___x_1059_, v_head_1067_, v_ctors_1072_, v___x_1073_, v___y_1062_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_head_1067_);
lean_ctor_set(v___x_1076_, 1, v_a_1075_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_x_1061_);
lean_ctor_set(v___x_1070_, 0, v___x_1076_);
v___x_1078_ = v___x_1070_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_x_1061_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v_x_1060_ = v_tail_1068_;
v_x_1061_ = v___x_1078_;
goto _start;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_del_object(v___x_1070_);
lean_dec(v_tail_1068_);
lean_dec(v_head_1067_);
lean_dec(v_x_1061_);
v_a_1081_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1074_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1074_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9___boxed(lean_object* v___x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v___x_39685__boxed_1096_; lean_object* v_res_1097_; 
v___x_39685__boxed_1096_ = lean_unbox(v___x_1090_);
v_res_1097_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(v___x_39685__boxed_1096_, v_x_1091_, v_x_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(lean_object* v_as_x27_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_){
_start:
{
if (lean_obj_tag(v_as_x27_1098_) == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_b_1099_);
return v___x_1102_;
}
else
{
lean_object* v_head_1103_; lean_object* v_tail_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_toConstantVal_1107_; lean_object* v_env_1108_; lean_object* v_remaining_1109_; lean_object* v_pending_1110_; lean_object* v_postponedConstructors_1111_; lean_object* v_postponedRecursors_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1124_; 
v_head_1103_ = lean_ctor_get(v_as_x27_1098_, 0);
v_tail_1104_ = lean_ctor_get(v_as_x27_1098_, 1);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_st_ref_take(v___y_1100_);
v_toConstantVal_1107_ = lean_ctor_get(v_head_1103_, 0);
v_env_1108_ = lean_ctor_get(v___x_1106_, 0);
v_remaining_1109_ = lean_ctor_get(v___x_1106_, 1);
v_pending_1110_ = lean_ctor_get(v___x_1106_, 2);
v_postponedConstructors_1111_ = lean_ctor_get(v___x_1106_, 3);
v_postponedRecursors_1112_ = lean_ctor_get(v___x_1106_, 4);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1114_ = v___x_1106_;
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_postponedRecursors_1112_);
lean_inc(v_postponedConstructors_1111_);
lean_inc(v_pending_1110_);
lean_inc(v_remaining_1109_);
lean_inc(v_env_1108_);
lean_dec(v___x_1106_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1124_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_name_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_name_1116_ = lean_ctor_get(v_toConstantVal_1107_, 0);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_1116_, v_remaining_1109_);
v___x_1118_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo_spec__0___redArg(v_name_1116_, v_pending_1110_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v___x_1118_);
lean_ctor_set(v___x_1114_, 1, v___x_1117_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_env_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_postponedConstructors_1111_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_postponedRecursors_1112_);
v___x_1120_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_st_ref_put(v___y_1100_, v___x_1120_);
v_as_x27_1098_ = v_tail_1104_;
v_b_1099_ = v___x_1105_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg___boxed(lean_object* v_as_x27_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1125_, v_b_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec(v_as_x27_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
if (lean_obj_tag(v_x_1130_) == 0)
{
if (lean_obj_tag(v_x_1131_) == 0)
{
uint8_t v___x_1132_; 
v___x_1132_ = 1;
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
return v___x_1133_;
}
}
else
{
if (lean_obj_tag(v_x_1131_) == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = 0;
return v___x_1134_;
}
else
{
lean_object* v_head_1135_; lean_object* v_tail_1136_; lean_object* v_head_1137_; lean_object* v_tail_1138_; uint8_t v___x_1139_; 
v_head_1135_ = lean_ctor_get(v_x_1130_, 0);
v_tail_1136_ = lean_ctor_get(v_x_1130_, 1);
v_head_1137_ = lean_ctor_get(v_x_1131_, 0);
v_tail_1138_ = lean_ctor_get(v_x_1131_, 1);
v___x_1139_ = lean_name_eq(v_head_1135_, v_head_1137_);
if (v___x_1139_ == 0)
{
return v___x_1139_;
}
else
{
v_x_1130_ = v_tail_1136_;
v_x_1131_ = v_tail_1138_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3___boxed(lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_res_1143_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(v_x_1141_, v_x_1142_);
lean_dec(v_x_1142_);
lean_dec(v_x_1141_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg(uint8_t v___x_1146_, lean_object* v_as_x27_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_){
_start:
{
if (lean_obj_tag(v_as_x27_1147_) == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_b_1148_);
return v___x_1151_;
}
else
{
lean_object* v_head_1152_; lean_object* v_tail_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_toConstantVal_1156_; lean_object* v_env_1157_; lean_object* v_name_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_head_1152_ = lean_ctor_get(v_as_x27_1147_, 0);
v_tail_1153_ = lean_ctor_get(v_as_x27_1147_, 1);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_st_ref_get(v___y_1149_);
v_toConstantVal_1156_ = lean_ctor_get(v_head_1152_, 0);
v_env_1157_ = lean_ctor_get(v___x_1155_, 0);
lean_inc_ref(v_env_1157_);
lean_dec(v___x_1155_);
v_name_1158_ = lean_ctor_get(v_toConstantVal_1156_, 0);
lean_inc(v_name_1158_);
v___x_1159_ = lean_environment_find(v_env_1157_, v_name_1158_);
lean_inc(v_head_1152_);
v___x_1160_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_head_1152_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
v___x_1162_ = l_instBEqOption_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__6(v___x_1159_, v___x_1161_);
lean_dec_ref_known(v___x_1161_, 1);
lean_dec(v___x_1159_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1163_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___closed__0));
lean_inc(v_name_1158_);
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1158_, v___x_1146_);
v___x_1165_ = lean_string_append(v___x_1163_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
else
{
v_as_x27_1147_ = v_tail_1153_;
v_b_1148_ = v___x_1154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg___boxed(lean_object* v___x_1169_, lean_object* v_as_x27_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v___x_39817__boxed_1174_; lean_object* v_res_1175_; 
v___x_39817__boxed_1174_ = lean_unbox(v___x_1169_);
v_res_1175_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg(v___x_39817__boxed_1174_, v_as_x27_1170_, v_b_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec(v_as_x27_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg(lean_object* v_as_x27_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
if (lean_obj_tag(v_as_x27_1183_) == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1184_);
return v___x_1188_;
}
else
{
lean_object* v_head_1189_; lean_object* v_tail_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_head_1189_ = lean_ctor_get(v_as_x27_1183_, 0);
v_tail_1190_ = lean_ctor_get(v_as_x27_1183_, 1);
v___x_1191_ = lean_box(0);
lean_inc(v_head_1189_);
v___x_1192_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_head_1189_);
v___x_1193_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1192_, v___y_1185_, v___y_1186_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref_known(v___x_1193_, 1);
v_as_x27_1183_ = v_tail_1190_;
v_b_1184_ = v___x_1191_;
goto _start;
}
else
{
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg(lean_object* v_as_x27_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
if (lean_obj_tag(v_as_x27_1195_) == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_b_1196_);
return v___x_1200_;
}
else
{
lean_object* v_head_1201_; lean_object* v_tail_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_head_1201_ = lean_ctor_get(v_as_x27_1195_, 0);
v_tail_1202_ = lean_ctor_get(v_as_x27_1195_, 1);
v_fst_1203_ = lean_ctor_get(v_head_1201_, 0);
v_snd_1204_ = lean_ctor_get(v_head_1201_, 1);
v___x_1205_ = lean_box(0);
lean_inc(v_fst_1203_);
v___x_1206_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_fst_1203_);
v___x_1207_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v___x_1206_);
v___x_1208_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1207_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1208_, 1);
v___x_1209_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg(v_snd_1204_, v___x_1205_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref_known(v___x_1209_, 1);
v_as_x27_1195_ = v_tail_1202_;
v_b_1196_ = v___x_1205_;
goto _start;
}
else
{
return v___x_1209_;
}
}
else
{
return v___x_1208_;
}
}
}
}
static lean_object* _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__8));
v___x_1215_ = lean_unsigned_to_nat(50u);
v___x_1216_ = lean_unsigned_to_nat(76u);
v___x_1217_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__7));
v___x_1218_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__6));
v___x_1219_ = l_mkPanicMessageWithDecl(v___x_1218_, v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(lean_object* v_name_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___f_1224_; lean_object* v___x_1225_; 
lean_inc_n(v_name_1220_, 2);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1224_, 0, v_name_1220_);
v___x_1225_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_isTodo___redArg(v_name_1220_, v_a_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1437_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1437_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1437_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_unbox(v_a_1226_);
lean_dec(v_a_1226_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
v___x_1231_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
else
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v_a_1221_, v_name_1220_);
if (lean_obj_tag(v___x_1235_) == 1)
{
lean_object* v_val_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1434_; 
v_val_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1434_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_val_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1434_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_inc(v_val_1236_);
v___x_1240_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_1236_);
v___x_1241_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v___x_1240_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1432_; 
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1433_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1432_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1432_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v_pending_1246_; uint8_t v___x_1247_; lean_object* v_a_1249_; lean_object* v___y_1264_; 
v___x_1245_ = lean_st_ref_get(v_a_1222_);
v_pending_1246_ = lean_ctor_get(v___x_1245_, 2);
lean_inc(v_pending_1246_);
lean_dec(v___x_1245_);
v___x_1247_ = l_Lean_NameSet_contains(v_pending_1246_, v_name_1220_);
lean_dec(v_pending_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_del_object(v___x_1243_);
lean_del_object(v___x_1238_);
lean_dec(v_val_1236_);
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
v___x_1275_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1275_);
v___x_1277_ = v___x_1228_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
else
{
switch(lean_obj_tag(v_val_1236_))
{
case 0:
{
lean_object* v_val_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1279_ = lean_ctor_get(v_val_1236_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_val_1236_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1281_ = v_val_1236_;
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_val_1279_);
lean_dec(v_val_1236_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_val_1279_);
v___x_1284_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1284_, v_a_1222_);
lean_dec_ref(v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v_a_1286_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1287_;
goto v___jp_1263_;
}
else
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1285_, 1);
v_a_1249_ = v_a_1288_;
goto v___jp_1248_;
}
}
}
}
case 1:
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1302_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1291_ = lean_ctor_get(v_val_1236_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_val_1236_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1293_ = v_val_1236_;
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_val_1236_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1291_);
v___x_1296_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1296_, v_a_1222_);
lean_dec_ref(v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v_a_1298_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1299_;
goto v___jp_1263_;
}
else
{
lean_object* v_a_1300_; 
v_a_1300_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1297_, 1);
v_a_1249_ = v_a_1300_;
goto v___jp_1248_;
}
}
}
}
case 2:
{
lean_object* v_val_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v_env_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_val_1303_ = lean_ctor_get(v_val_1236_, 0);
lean_inc_ref_n(v_val_1303_, 2);
lean_inc_ref(v___f_1224_);
v___f_1304_ = lean_alloc_closure((void*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1___boxed), 6, 2);
lean_closure_set(v___f_1304_, 0, v_val_1303_);
lean_closure_set(v___f_1304_, 1, v___f_1224_);
v___x_1305_ = lean_st_ref_get(v_a_1222_);
v_env_1309_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1305_);
v___x_1310_ = l_Lean_ConstantInfo_name(v_val_1236_);
lean_dec_ref_known(v_val_1236_, 1);
v___x_1311_ = lean_environment_find(v_env_1309_, v___x_1310_);
if (lean_obj_tag(v___x_1311_) == 1)
{
lean_object* v_val_1312_; 
v_val_1312_ = lean_ctor_get(v___x_1311_, 0);
if (lean_obj_tag(v_val_1312_) == 2)
{
lean_object* v_toConstantVal_1313_; lean_object* v_val_1314_; lean_object* v_toConstantVal_1315_; lean_object* v_all_1316_; lean_object* v_name_1317_; lean_object* v_levelParams_1318_; lean_object* v_type_1319_; lean_object* v_all_1320_; lean_object* v_name_1321_; lean_object* v_levelParams_1322_; lean_object* v_type_1323_; uint8_t v___x_1324_; 
lean_inc_ref(v_val_1312_);
lean_dec_ref_known(v___x_1311_, 1);
lean_dec_ref(v___f_1304_);
v_toConstantVal_1313_ = lean_ctor_get(v_val_1303_, 0);
v_val_1314_ = lean_ctor_get(v_val_1312_, 0);
lean_inc_ref(v_val_1314_);
lean_dec_ref_known(v_val_1312_, 1);
v_toConstantVal_1315_ = lean_ctor_get(v_val_1314_, 0);
lean_inc_ref(v_toConstantVal_1315_);
v_all_1316_ = lean_ctor_get(v_val_1303_, 2);
v_name_1317_ = lean_ctor_get(v_toConstantVal_1313_, 0);
v_levelParams_1318_ = lean_ctor_get(v_toConstantVal_1313_, 1);
v_type_1319_ = lean_ctor_get(v_toConstantVal_1313_, 2);
v_all_1320_ = lean_ctor_get(v_val_1314_, 2);
lean_inc(v_all_1320_);
lean_dec_ref(v_val_1314_);
v_name_1321_ = lean_ctor_get(v_toConstantVal_1315_, 0);
lean_inc(v_name_1321_);
v_levelParams_1322_ = lean_ctor_get(v_toConstantVal_1315_, 1);
lean_inc(v_levelParams_1322_);
v_type_1323_ = lean_ctor_get(v_toConstantVal_1315_, 2);
lean_inc_ref(v_type_1323_);
lean_dec_ref(v_toConstantVal_1315_);
v___x_1324_ = lean_name_eq(v_name_1317_, v_name_1321_);
lean_dec(v_name_1321_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v_type_1323_);
lean_dec(v_levelParams_1322_);
lean_dec(v_all_1320_);
lean_del_object(v___x_1228_);
goto v___jp_1306_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_expr_eqv(v_type_1319_, v_type_1323_);
lean_dec_ref(v_type_1323_);
if (v___x_1325_ == 0)
{
lean_dec(v_levelParams_1322_);
lean_dec(v_all_1320_);
lean_del_object(v___x_1228_);
goto v___jp_1306_;
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(v_levelParams_1318_, v_levelParams_1322_);
lean_dec(v_levelParams_1322_);
if (v___x_1326_ == 0)
{
lean_dec(v_all_1320_);
lean_del_object(v___x_1228_);
goto v___jp_1306_;
}
else
{
uint8_t v___x_1327_; 
v___x_1327_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__3(v_all_1316_, v_all_1320_);
lean_dec(v_all_1320_);
if (v___x_1327_ == 0)
{
lean_del_object(v___x_1228_);
goto v___jp_1306_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec_ref(v_val_1303_);
lean_del_object(v___x_1243_);
lean_del_object(v___x_1238_);
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
v___x_1328_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1328_);
v___x_1330_ = v___x_1228_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v_val_1303_);
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v___x_1332_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1304_, v___x_1311_, v_a_1221_, v_a_1222_);
lean_dec_ref_known(v___x_1311_, 1);
v___y_1264_ = v___x_1332_;
goto v___jp_1263_;
}
}
else
{
lean_object* v___x_1333_; 
lean_dec_ref(v_val_1303_);
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v___x_1333_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__2(v___f_1304_, v___x_1311_, v_a_1221_, v_a_1222_);
lean_dec(v___x_1311_);
v___y_1264_ = v___x_1333_;
goto v___jp_1263_;
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_box(0);
v___x_1308_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__1(v_val_1303_, v___f_1224_, v___x_1307_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1308_;
goto v___jp_1263_;
}
}
case 3:
{
lean_object* v_val_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1345_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1334_ = lean_ctor_get(v_val_1236_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_val_1236_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1336_ = v_val_1236_;
v_isShared_1337_ = v_isSharedCheck_1345_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_val_1334_);
lean_dec(v_val_1236_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1345_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_val_1334_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1339_, v_a_1222_);
lean_dec_ref(v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1342_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v_a_1341_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1342_;
goto v___jp_1263_;
}
else
{
lean_object* v_a_1343_; 
v_a_1343_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1340_, 1);
v_a_1249_ = v_a_1343_;
goto v___jp_1248_;
}
}
}
}
case 4:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref_known(v_val_1236_, 1);
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v___x_1346_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__3));
v___x_1347_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v___x_1346_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = lean_box(4);
v___x_1349_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1348_, v_a_1222_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v_a_1350_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1351_;
goto v___jp_1263_;
}
else
{
lean_object* v_a_1352_; 
v_a_1352_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1349_, 1);
v_a_1249_ = v_a_1352_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1353_; 
v_a_1353_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1347_, 1);
v_a_1249_ = v_a_1353_;
goto v___jp_1248_;
}
}
case 5:
{
lean_object* v_val_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1391_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1354_ = lean_ctor_get(v_val_1236_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_val_1236_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1356_ = v_val_1236_;
v_isShared_1357_ = v_isSharedCheck_1391_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_val_1354_);
lean_dec(v_val_1236_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1391_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v_toConstantVal_1358_; lean_object* v_numParams_1359_; lean_object* v_all_1360_; uint8_t v___x_1361_; 
v_toConstantVal_1358_ = lean_ctor_get(v_val_1354_, 0);
lean_inc_ref(v_toConstantVal_1358_);
v_numParams_1359_ = lean_ctor_get(v_val_1354_, 1);
lean_inc(v_numParams_1359_);
v_all_1360_ = lean_ctor_get(v_val_1354_, 3);
lean_inc(v_all_1360_);
lean_dec_ref(v_val_1354_);
v___x_1361_ = l_List_elem___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v_name_1220_, v_all_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec(v_all_1360_);
lean_dec(v_numParams_1359_);
lean_dec_ref(v_toConstantVal_1358_);
v___x_1362_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__4));
lean_inc(v_name_1220_);
v___x_1363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1220_, v___x_1247_);
v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__5));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 18);
lean_ctor_set(v___x_1356_, 0, v___x_1366_);
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
v_a_1249_ = v___x_1368_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_levelParams_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_del_object(v___x_1356_);
v_levelParams_1370_ = lean_ctor_get(v_toConstantVal_1358_, 1);
lean_inc(v_levelParams_1370_);
lean_dec_ref(v_toConstantVal_1358_);
v___x_1371_ = lean_box(0);
lean_inc(v_name_1220_);
v___x_1372_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v___x_1247_, v_name_1220_, v_all_1360_, v___x_1371_, v_a_1221_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_box(0);
v___x_1375_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_a_1373_, v___x_1374_, v_a_1222_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref_known(v___x_1375_, 1);
lean_inc(v_a_1373_);
v___x_1376_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__9(v___x_1247_, v_a_1373_, v___x_1371_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg(v_a_1377_, v___x_1374_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec_ref_known(v___x_1378_, 1);
v___x_1379_ = l_List_mapTR_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__11(v_a_1377_, v___x_1371_);
v___x_1380_ = 0;
v___x_1381_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1381_, 0, v_levelParams_1370_);
lean_ctor_set(v___x_1381_, 1, v_numParams_1359_);
lean_ctor_set(v___x_1381_, 2, v___x_1379_);
lean_ctor_set_uint8(v___x_1381_, sizeof(void*)*3, v___x_1380_);
v___x_1382_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_addDecl___redArg(v___x_1381_, v_a_1222_);
lean_dec_ref_known(v___x_1381_, 3);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1382_, 1);
v___x_1383_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg(v___x_1247_, v_a_1373_, v___x_1374_, v_a_1222_);
lean_dec(v_a_1373_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1383_, 1);
v___x_1384_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v___x_1374_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1384_;
goto v___jp_1263_;
}
else
{
lean_object* v_a_1385_; 
v_a_1385_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1383_, 1);
v_a_1249_ = v_a_1385_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1386_; 
lean_dec(v_a_1373_);
v_a_1386_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1382_, 1);
v_a_1249_ = v_a_1386_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1387_; 
lean_dec(v_a_1377_);
lean_dec(v_a_1373_);
lean_dec(v_levelParams_1370_);
lean_dec(v_numParams_1359_);
v_a_1387_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1378_, 1);
v_a_1249_ = v_a_1387_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1388_; 
lean_dec(v_a_1373_);
lean_dec(v_levelParams_1370_);
lean_dec(v_numParams_1359_);
v_a_1388_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1376_, 1);
v_a_1249_ = v_a_1388_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1389_; 
lean_dec(v_a_1373_);
lean_dec(v_levelParams_1370_);
lean_dec(v_numParams_1359_);
v_a_1389_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1375_, 1);
v_a_1249_ = v_a_1389_;
goto v___jp_1248_;
}
}
else
{
lean_object* v_a_1390_; 
lean_dec(v_levelParams_1370_);
lean_dec(v_numParams_1359_);
v_a_1390_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1372_, 1);
v_a_1249_ = v_a_1390_;
goto v___jp_1248_;
}
}
}
}
case 6:
{
lean_object* v_val_1392_; lean_object* v___x_1393_; lean_object* v_toConstantVal_1394_; lean_object* v_env_1395_; lean_object* v_remaining_1396_; lean_object* v_pending_1397_; lean_object* v_postponedConstructors_1398_; lean_object* v_postponedRecursors_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1411_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1392_ = lean_ctor_get(v_val_1236_, 0);
lean_inc_ref(v_val_1392_);
lean_dec_ref_known(v_val_1236_, 1);
v___x_1393_ = lean_st_ref_take(v_a_1222_);
v_toConstantVal_1394_ = lean_ctor_get(v_val_1392_, 0);
lean_inc_ref(v_toConstantVal_1394_);
lean_dec_ref(v_val_1392_);
v_env_1395_ = lean_ctor_get(v___x_1393_, 0);
v_remaining_1396_ = lean_ctor_get(v___x_1393_, 1);
v_pending_1397_ = lean_ctor_get(v___x_1393_, 2);
v_postponedConstructors_1398_ = lean_ctor_get(v___x_1393_, 3);
v_postponedRecursors_1399_ = lean_ctor_get(v___x_1393_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1401_ = v___x_1393_;
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_postponedRecursors_1399_);
lean_inc(v_postponedConstructors_1398_);
lean_inc(v_pending_1397_);
lean_inc(v_remaining_1396_);
lean_inc(v_env_1395_);
lean_dec(v___x_1393_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_name_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v_name_1403_ = lean_ctor_get(v_toConstantVal_1394_, 0);
lean_inc(v_name_1403_);
lean_dec_ref(v_toConstantVal_1394_);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_Lean_NameSet_insert(v_postponedConstructors_1398_, v_name_1403_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 3, v___x_1405_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_env_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_remaining_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_pending_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_postponedRecursors_1399_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_st_ref_put(v_a_1222_, v___x_1407_);
v___x_1409_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v___x_1404_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1409_;
goto v___jp_1263_;
}
}
}
default: 
{
lean_object* v_val_1412_; lean_object* v___x_1413_; lean_object* v_toConstantVal_1414_; lean_object* v_env_1415_; lean_object* v_remaining_1416_; lean_object* v_pending_1417_; lean_object* v_postponedConstructors_1418_; lean_object* v_postponedRecursors_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1431_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
v_val_1412_ = lean_ctor_get(v_val_1236_, 0);
lean_inc_ref(v_val_1412_);
lean_dec_ref_known(v_val_1236_, 1);
v___x_1413_ = lean_st_ref_take(v_a_1222_);
v_toConstantVal_1414_ = lean_ctor_get(v_val_1412_, 0);
lean_inc_ref(v_toConstantVal_1414_);
lean_dec_ref(v_val_1412_);
v_env_1415_ = lean_ctor_get(v___x_1413_, 0);
v_remaining_1416_ = lean_ctor_get(v___x_1413_, 1);
v_pending_1417_ = lean_ctor_get(v___x_1413_, 2);
v_postponedConstructors_1418_ = lean_ctor_get(v___x_1413_, 3);
v_postponedRecursors_1419_ = lean_ctor_get(v___x_1413_, 4);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1421_ = v___x_1413_;
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_postponedRecursors_1419_);
lean_inc(v_postponedConstructors_1418_);
lean_inc(v_pending_1417_);
lean_inc(v_remaining_1416_);
lean_inc(v_env_1415_);
lean_dec(v___x_1413_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1431_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_name_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v_name_1423_ = lean_ctor_get(v_toConstantVal_1414_, 0);
lean_inc(v_name_1423_);
lean_dec_ref(v_toConstantVal_1414_);
v___x_1424_ = lean_box(0);
v___x_1425_ = l_Lean_NameSet_insert(v_postponedRecursors_1419_, v_name_1423_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v___x_1425_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_env_1415_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_remaining_1416_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_pending_1417_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_postponedConstructors_1418_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_st_ref_put(v_a_1222_, v___x_1427_);
v___x_1429_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___lam__0(v_name_1220_, v___x_1424_, v_a_1221_, v_a_1222_);
v___y_1264_ = v___x_1429_;
goto v___jp_1263_;
}
}
}
}
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__0));
v___x_1251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1220_, v___x_1247_);
v___x_1252_ = lean_string_append(v___x_1250_, v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = ((lean_object*)(l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__1));
v___x_1254_ = lean_string_append(v___x_1252_, v___x_1253_);
v___x_1255_ = lean_io_error_to_string(v_a_1249_);
v___x_1256_ = lean_string_append(v___x_1254_, v___x_1255_);
lean_dec_ref(v___x_1255_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 18);
lean_ctor_set(v___x_1238_, 0, v___x_1256_);
v___x_1258_ = v___x_1238_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
lean_ctor_set(v___x_1243_, 0, v___x_1258_);
v___x_1260_ = v___x_1243_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
v___jp_1263_:
{
if (lean_obj_tag(v___y_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
lean_del_object(v___x_1243_);
lean_del_object(v___x_1238_);
lean_dec(v_name_1220_);
v_a_1265_ = lean_ctor_get(v___y_1264_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___y_1264_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___y_1264_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___y_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_a_1269_; lean_object* v___x_1271_; 
v_a_1269_ = lean_ctor_get(v_a_1265_, 0);
lean_inc(v_a_1269_);
lean_dec(v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_a_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_a_1274_; 
v_a_1274_ = lean_ctor_get(v___y_1264_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___y_1264_, 1);
v_a_1249_ = v_a_1274_;
goto v___jp_1248_;
}
}
}
}
else
{
lean_del_object(v___x_1238_);
lean_dec(v_val_1236_);
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v___x_1235_);
lean_del_object(v___x_1228_);
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
v___x_1435_ = lean_obj_once(&l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9, &l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9_once, _init_l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___closed__9);
v___x_1436_ = l_panic___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__13(v___x_1435_, v_a_1221_, v_a_1222_);
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___f_1224_);
lean_dec(v_name_1220_);
v_a_1438_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1225_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1225_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(lean_object* v_init_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
lean_object* v_k_1451_; lean_object* v_l_1452_; lean_object* v_r_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_k_1451_ = lean_ctor_get(v_x_1447_, 1);
lean_inc(v_k_1451_);
v_l_1452_ = lean_ctor_get(v_x_1447_, 3);
lean_inc(v_l_1452_);
v_r_1453_ = lean_ctor_get(v_x_1447_, 4);
lean_inc(v_r_1453_);
lean_dec_ref_known(v_x_1447_, 5);
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(v_init_1446_, v_l_1452_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref_known(v___x_1455_, 1);
v___x_1456_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_k_1451_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec_ref_known(v___x_1456_, 1);
v_init_1446_ = v___x_1454_;
v_x_1447_ = v_r_1453_;
goto _start;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_r_1453_);
v_a_1458_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1456_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1456_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_dec(v_r_1453_);
lean_dec(v_k_1451_);
return v___x_1455_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_init_1446_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(lean_object* v_names_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(v___x_1472_, v_names_1468_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1481_);
v___x_1475_ = v___x_1473_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v___x_1473_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1472_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1473_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1473_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants___boxed(lean_object* v_names_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants(v_names_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg___boxed(lean_object* v_as_x27_1495_, lean_object* v_b_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg(v_as_x27_1495_, v_b_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_as_x27_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg___boxed(lean_object* v_as_x27_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg(v_as_x27_1501_, v_b_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v_as_x27_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15___boxed(lean_object* v_init_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(v_init_1507_, v_x_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant___boxed(lean_object* v_name_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v_name_1513_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(lean_object* v_00_u03b2_1518_, lean_object* v_m_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v_m_1519_, v_a_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1(v_00_u03b2_1522_, v_m_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_m_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(uint8_t v___x_1526_, lean_object* v_val_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___redArg(v___x_1526_, v_val_1527_, v_x_1528_, v_x_1529_, v___y_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2___boxed(lean_object* v___x_1534_, lean_object* v_val_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_40457__boxed_1541_; lean_object* v_res_1542_; 
v___x_40457__boxed_1541_ = lean_unbox(v___x_1534_);
v_res_1542_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__2(v___x_40457__boxed_1541_, v_val_1535_, v_x_1536_, v_x_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(uint8_t v___x_1543_, lean_object* v_name_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg(v___x_1543_, v_name_1544_, v_x_1545_, v_x_1546_, v___y_1547_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___boxed(lean_object* v___x_1551_, lean_object* v_name_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v___x_40477__boxed_1558_; lean_object* v_res_1559_; 
v___x_40477__boxed_1558_ = lean_unbox(v___x_1551_);
v_res_1559_ = l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5(v___x_40477__boxed_1558_, v_name_1552_, v_x_1553_, v_x_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(lean_object* v_as_1560_, lean_object* v_as_x27_1561_, lean_object* v_b_1562_, lean_object* v_a_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___redArg(v_as_x27_1561_, v_b_1562_, v___y_1564_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7___boxed(lean_object* v_as_1568_, lean_object* v_as_x27_1569_, lean_object* v_b_1570_, lean_object* v_a_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__7(v_as_1568_, v_as_x27_1569_, v_b_1570_, v_a_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_as_x27_1569_);
lean_dec(v_as_1568_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(lean_object* v_as_1576_, lean_object* v_as_x27_1577_, lean_object* v_b_1578_, lean_object* v_a_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___redArg(v_as_x27_1577_, v_b_1578_, v___y_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8___boxed(lean_object* v_as_1584_, lean_object* v_as_x27_1585_, lean_object* v_b_1586_, lean_object* v_a_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__8(v_as_1584_, v_as_x27_1585_, v_b_1586_, v_a_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v_as_x27_1585_);
lean_dec(v_as_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(lean_object* v_as_1592_, lean_object* v_as_x27_1593_, lean_object* v_b_1594_, lean_object* v_a_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___redArg(v_as_x27_1593_, v_b_1594_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10___boxed(lean_object* v_as_1600_, lean_object* v_as_x27_1601_, lean_object* v_b_1602_, lean_object* v_a_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__10(v_as_1600_, v_as_x27_1601_, v_b_1602_, v_a_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v_as_x27_1601_);
lean_dec(v_as_1600_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12(uint8_t v___x_1608_, lean_object* v_as_1609_, lean_object* v_as_x27_1610_, lean_object* v_b_1611_, lean_object* v_a_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___redArg(v___x_1608_, v_as_x27_1610_, v_b_1611_, v___y_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12___boxed(lean_object* v___x_1617_, lean_object* v_as_1618_, lean_object* v_as_x27_1619_, lean_object* v_b_1620_, lean_object* v_a_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
uint8_t v___x_40539__boxed_1625_; lean_object* v_res_1626_; 
v___x_40539__boxed_1625_ = lean_unbox(v___x_1617_);
v_res_1626_ = l_List_forIn_x27_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__12(v___x_40539__boxed_1625_, v_as_1618_, v_as_x27_1619_, v_b_1620_, v_a_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v_as_x27_1619_);
lean_dec(v_as_1618_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(lean_object* v_00_u03b2_1627_, lean_object* v_a_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___redArg(v_a_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_a_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1_spec__1(v_00_u03b2_1631_, v_a_1632_, v_x_1633_);
lean_dec(v_x_1633_);
lean_dec(v_a_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(lean_object* v_init_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
lean_object* v_k_1642_; lean_object* v_l_1643_; lean_object* v_r_1644_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_k_1642_ = lean_ctor_get(v_x_1638_, 1);
lean_inc(v_k_1642_);
v_l_1643_ = lean_ctor_get(v_x_1638_, 3);
lean_inc(v_l_1643_);
v_r_1644_ = lean_ctor_get(v_x_1638_, 4);
lean_inc(v_r_1644_);
lean_dec_ref_known(v_x_1638_, 5);
v___x_1652_ = lean_box(0);
v___x_1653_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1637_, v_l_1643_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1675_; 
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1653_, 0);
lean_dec(v_unused_1676_);
v___x_1655_ = v___x_1653_;
v_isShared_1656_ = v_isSharedCheck_1675_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v___x_1653_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1675_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v_env_1658_; lean_object* v___x_1659_; 
v___x_1657_ = lean_st_ref_get(v___y_1640_);
v_env_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc_ref(v_env_1658_);
lean_dec(v___x_1657_);
lean_inc(v_k_1642_);
v___x_1659_ = lean_environment_find(v_env_1658_, v_k_1642_);
if (lean_obj_tag(v___x_1659_) == 1)
{
lean_object* v_val_1660_; 
v_val_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v___x_1659_, 1);
if (lean_obj_tag(v_val_1660_) == 6)
{
lean_object* v_val_1661_; lean_object* v___x_1662_; 
v_val_1661_ = lean_ctor_get(v_val_1660_, 0);
lean_inc_ref(v_val_1661_);
lean_dec_ref_known(v_val_1660_, 1);
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v___y_1639_, v_k_1642_);
if (lean_obj_tag(v___x_1662_) == 1)
{
lean_object* v_val_1663_; 
v_val_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v___x_1662_, 1);
if (lean_obj_tag(v_val_1663_) == 6)
{
lean_object* v_val_1664_; uint8_t v___x_1665_; 
v_val_1664_ = lean_ctor_get(v_val_1663_, 0);
lean_inc_ref(v_val_1664_);
lean_dec_ref_known(v_val_1663_, 1);
v___x_1665_ = l_Lean_instBEqConstructorVal_beq(v_val_1661_, v_val_1664_);
lean_dec_ref(v_val_1664_);
lean_dec_ref(v_val_1661_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_dec(v_r_1644_);
v___x_1666_ = 1;
v___x_1667_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__1));
v___x_1668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1642_, v___x_1666_);
v___x_1669_ = lean_string_append(v___x_1667_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = lean_mk_io_user_error(v___x_1669_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1670_);
v___x_1672_ = v___x_1655_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
else
{
lean_del_object(v___x_1655_);
lean_dec(v_k_1642_);
v_init_1637_ = v___x_1652_;
v_x_1638_ = v_r_1644_;
goto _start;
}
}
else
{
lean_dec(v_val_1663_);
lean_dec_ref(v_val_1661_);
lean_del_object(v___x_1655_);
lean_dec(v_r_1644_);
goto v___jp_1645_;
}
}
else
{
lean_dec(v___x_1662_);
lean_dec_ref(v_val_1661_);
lean_del_object(v___x_1655_);
lean_dec(v_r_1644_);
goto v___jp_1645_;
}
}
else
{
lean_dec(v_val_1660_);
lean_del_object(v___x_1655_);
lean_dec(v_r_1644_);
goto v___jp_1645_;
}
}
else
{
lean_dec(v___x_1659_);
lean_del_object(v___x_1655_);
lean_dec(v_r_1644_);
goto v___jp_1645_;
}
}
}
else
{
lean_dec(v_r_1644_);
lean_dec(v_k_1642_);
return v___x_1653_;
}
v___jp_1645_:
{
lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___closed__0));
v___x_1647_ = 1;
v___x_1648_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1642_, v___x_1647_);
v___x_1649_ = lean_string_append(v___x_1646_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = lean_mk_io_user_error(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_init_1637_);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object* v_init_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v_init_1679_, v_x_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v_postponedConstructors_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_st_ref_get(v_a_1686_);
v_postponedConstructors_1689_ = lean_ctor_get(v___x_1688_, 3);
lean_inc(v_postponedConstructors_1689_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_box(0);
v___x_1691_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors_spec__0(v___x_1690_, v_postponedConstructors_1689_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v___x_1691_, 0);
lean_dec(v_unused_1699_);
v___x_1693_ = v___x_1691_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v___x_1691_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1690_);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1690_);
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
v_a_1700_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1691_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1691_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors___boxed(lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(lean_object* v_init_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v_k_1719_; lean_object* v_l_1720_; lean_object* v_r_1721_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_k_1719_ = lean_ctor_get(v_x_1715_, 1);
lean_inc(v_k_1719_);
v_l_1720_ = lean_ctor_get(v_x_1715_, 3);
lean_inc(v_l_1720_);
v_r_1721_ = lean_ctor_get(v_x_1715_, 4);
lean_inc(v_r_1721_);
lean_dec_ref_known(v_x_1715_, 5);
v___x_1729_ = lean_box(0);
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1714_, v_l_1720_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1730_, 0);
lean_dec(v_unused_1753_);
v___x_1732_ = v___x_1730_;
v_isShared_1733_ = v_isSharedCheck_1752_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v___x_1730_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1752_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v_env_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_st_ref_get(v___y_1717_);
v_env_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_env_1735_);
lean_dec(v___x_1734_);
lean_inc(v_k_1719_);
v___x_1736_ = lean_environment_find(v_env_1735_, v_k_1719_);
if (lean_obj_tag(v___x_1736_) == 1)
{
lean_object* v_val_1737_; 
v_val_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v___x_1736_, 1);
if (lean_obj_tag(v_val_1737_) == 7)
{
lean_object* v_val_1738_; lean_object* v___x_1739_; 
v_val_1738_ = lean_ctor_get(v_val_1737_, 0);
lean_inc_ref(v_val_1738_);
lean_dec_ref_known(v_val_1737_, 1);
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__1___redArg(v___y_1716_, v_k_1719_);
if (lean_obj_tag(v___x_1739_) == 1)
{
lean_object* v_val_1740_; 
v_val_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_val_1740_);
lean_dec_ref_known(v___x_1739_, 1);
if (lean_obj_tag(v_val_1740_) == 7)
{
lean_object* v_val_1741_; uint8_t v___x_1742_; 
v_val_1741_ = lean_ctor_get(v_val_1740_, 0);
lean_inc_ref(v_val_1741_);
lean_dec_ref_known(v_val_1740_, 1);
v___x_1742_ = l_Lean_instBEqRecursorVal_beq(v_val_1738_, v_val_1741_);
lean_dec_ref(v_val_1741_);
lean_dec_ref(v_val_1738_);
if (v___x_1742_ == 0)
{
uint8_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_r_1721_);
v___x_1743_ = 1;
v___x_1744_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__1));
v___x_1745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1719_, v___x_1743_);
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = lean_mk_io_user_error(v___x_1746_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 1);
lean_ctor_set(v___x_1732_, 0, v___x_1747_);
v___x_1749_ = v___x_1732_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
else
{
lean_del_object(v___x_1732_);
lean_dec(v_k_1719_);
v_init_1714_ = v___x_1729_;
v_x_1715_ = v_r_1721_;
goto _start;
}
}
else
{
lean_dec(v_val_1740_);
lean_dec_ref(v_val_1738_);
lean_del_object(v___x_1732_);
lean_dec(v_r_1721_);
goto v___jp_1722_;
}
}
else
{
lean_dec(v___x_1739_);
lean_dec_ref(v_val_1738_);
lean_del_object(v___x_1732_);
lean_dec(v_r_1721_);
goto v___jp_1722_;
}
}
else
{
lean_dec(v_val_1737_);
lean_del_object(v___x_1732_);
lean_dec(v_r_1721_);
goto v___jp_1722_;
}
}
else
{
lean_dec(v___x_1736_);
lean_del_object(v___x_1732_);
lean_dec(v_r_1721_);
goto v___jp_1722_;
}
}
}
else
{
lean_dec(v_r_1721_);
lean_dec(v_k_1719_);
return v___x_1730_;
}
v___jp_1722_:
{
lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___closed__0));
v___x_1724_ = 1;
v___x_1725_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_k_1719_, v___x_1724_);
v___x_1726_ = lean_string_append(v___x_1723_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = lean_mk_io_user_error(v___x_1726_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_init_1714_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object* v_init_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v_init_1756_, v_x_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v_postponedRecursors_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1765_ = lean_st_ref_get(v_a_1763_);
v_postponedRecursors_1766_ = lean_ctor_get(v___x_1765_, 4);
lean_inc(v_postponedRecursors_1766_);
lean_dec(v___x_1765_);
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors_spec__0(v___x_1767_, v_postponedRecursors_1766_, v_a_1762_, v_a_1763_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1776_);
v___x_1770_ = v___x_1768_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1768_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1767_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1767_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1768_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1768_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors___boxed(lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_inc(v_x_1789_);
return v_x_1789_;
}
else
{
lean_object* v_key_1791_; lean_object* v_value_1792_; lean_object* v_tail_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_key_1791_ = lean_ctor_get(v_x_1790_, 0);
v_value_1792_ = lean_ctor_get(v_x_1790_, 1);
v_tail_1793_ = lean_ctor_get(v_x_1790_, 2);
v___x_1794_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1789_, v_tail_1793_);
lean_inc(v_value_1792_);
lean_inc(v_key_1791_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_key_1791_);
lean_ctor_set(v___x_1795_, 1, v_value_1792_);
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1794_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1___boxed(lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_x_1797_, v_x_1798_);
lean_dec(v_x_1798_);
lean_dec(v_x_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(lean_object* v_as_1800_, size_t v_i_1801_, size_t v_stop_1802_, lean_object* v_b_1803_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_eq(v_i_1801_, v_stop_1802_);
if (v___x_1804_ == 0)
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = ((size_t)1ULL);
v___x_1806_ = lean_usize_sub(v_i_1801_, v___x_1805_);
v___x_1807_ = lean_array_uget_borrowed(v_as_1800_, v___x_1806_);
v___x_1808_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Kernel_Environment_replay_spec__1(v_b_1803_, v___x_1807_);
lean_dec(v_b_1803_);
v_i_1801_ = v___x_1806_;
v_b_1803_ = v___x_1808_;
goto _start;
}
else
{
return v_b_1803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2___boxed(lean_object* v_as_1810_, lean_object* v_i_1811_, lean_object* v_stop_1812_, lean_object* v_b_1813_){
_start:
{
size_t v_i_boxed_1814_; size_t v_stop_boxed_1815_; lean_object* v_res_1816_; 
v_i_boxed_1814_ = lean_unbox_usize(v_i_1811_);
lean_dec(v_i_1811_);
v_stop_boxed_1815_ = lean_unbox_usize(v_stop_1812_);
lean_dec(v_stop_1812_);
v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_as_1810_, v_i_boxed_1814_, v_stop_boxed_1815_, v_b_1813_);
lean_dec_ref(v_as_1810_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(lean_object* v_as_x27_1819_, lean_object* v_b_1820_){
_start:
{
if (lean_obj_tag(v_as_x27_1819_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_b_1820_);
return v___x_1822_;
}
else
{
lean_object* v_head_1823_; lean_object* v_tail_1824_; lean_object* v_fst_1825_; lean_object* v_snd_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_head_1823_ = lean_ctor_get(v_as_x27_1819_, 0);
v_tail_1824_ = lean_ctor_get(v_as_x27_1819_, 1);
v_fst_1825_ = lean_ctor_get(v_head_1823_, 0);
v_snd_1826_ = lean_ctor_get(v_head_1823_, 1);
v___x_1827_ = l_Lean_ConstantInfo_name(v_snd_1826_);
v___x_1828_ = lean_name_eq(v_fst_1825_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_b_1820_);
v___x_1829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__0));
v___x_1830_ = 1;
v___x_1831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1827_, v___x_1830_);
v___x_1832_ = lean_string_append(v___x_1829_, v___x_1831_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___closed__1));
v___x_1834_ = lean_string_append(v___x_1832_, v___x_1833_);
lean_inc(v_fst_1825_);
v___x_1835_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1825_, v___x_1830_);
v___x_1836_ = lean_string_append(v___x_1834_, v___x_1835_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__5___redArg___closed__0));
v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
else
{
uint8_t v___x_1841_; 
lean_dec(v___x_1827_);
v___x_1841_ = l_Lean_ConstantInfo_isUnsafe(v_snd_1826_);
if (v___x_1841_ == 0)
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_ConstantInfo_isPartial(v_snd_1826_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc(v_fst_1825_);
v___x_1843_ = l_Lean_NameSet_insert(v_b_1820_, v_fst_1825_);
v_as_x27_1819_ = v_tail_1824_;
v_b_1820_ = v___x_1843_;
goto _start;
}
else
{
v_as_x27_1819_ = v_tail_1824_;
goto _start;
}
}
else
{
v_as_x27_1819_ = v_tail_1824_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg___boxed(lean_object* v_as_x27_1847_, lean_object* v_b_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1847_, v_b_1848_);
lean_dec(v_as_x27_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay(lean_object* v_newConstants_1861_, lean_object* v_env_1862_){
_start:
{
lean_object* v_buckets_1864_; lean_object* v_remaining_1865_; lean_object* v___y_1867_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_buckets_1864_ = lean_ctor_get(v_newConstants_1861_, 1);
v_remaining_1865_ = l_Lean_NameSet_empty;
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_array_get_size(v_buckets_1864_);
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_nat_dec_lt(v___x_1940_, v___x_1939_);
if (v___x_1941_ == 0)
{
v___y_1867_ = v___x_1938_;
goto v___jp_1866_;
}
else
{
size_t v___x_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_usize_of_nat(v___x_1939_);
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_1864_, v___x_1942_, v___x_1943_, v___x_1938_);
v___y_1867_ = v___x_1944_;
goto v___jp_1866_;
}
v___jp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v___y_1867_, v_remaining_1865_);
lean_dec(v___y_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_n(v_a_1869_, 2);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = ((lean_object*)(l_Lean_Kernel_Environment_replay___closed__2));
v___x_1871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1871_, 0, v_env_1862_);
lean_ctor_set(v___x_1871_, 1, v_a_1869_);
lean_ctor_set(v___x_1871_, 2, v_remaining_1865_);
lean_ctor_set(v___x_1871_, 3, v_remaining_1865_);
lean_ctor_set(v___x_1871_, 4, v_remaining_1865_);
v___x_1872_ = lean_st_mk_ref(v___x_1871_);
v___x_1873_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v___x_1870_, v_newConstants_1861_, v___x_1872_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref_known(v___x_1873_, 1);
v___x_1874_ = ((lean_object*)(l_Lean_Kernel_Environment_replay___closed__5));
v___x_1875_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant(v___x_1874_, v_newConstants_1861_, v___x_1872_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref_known(v___x_1875_, 1);
v___x_1876_ = lean_box(0);
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstants_spec__15(v___x_1876_, v_a_1869_, v_newConstants_1861_, v___x_1872_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref_known(v___x_1877_, 1);
v___x_1878_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedConstructors(v_newConstants_1861_, v___x_1872_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; 
lean_dec_ref_known(v___x_1878_, 1);
v___x_1879_ = l___private_Lean_Replay_0__Lean_Kernel_Environment_Replay_checkPostponedRecursors(v_newConstants_1861_, v___x_1872_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1888_; 
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v___x_1879_, 0);
lean_dec(v_unused_1889_);
v___x_1881_ = v___x_1879_;
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v___x_1879_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v_env_1884_; lean_object* v___x_1886_; 
v___x_1883_ = lean_st_ref_get(v___x_1872_);
lean_dec(v___x_1872_);
v_env_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_env_1884_);
lean_dec(v___x_1883_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v_env_1884_);
v___x_1886_ = v___x_1881_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_env_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v___x_1872_);
v_a_1890_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1879_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1879_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___x_1872_);
v_a_1898_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1878_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1878_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v___x_1872_);
v_a_1906_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1877_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1877_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___x_1872_);
lean_dec(v_a_1869_);
v_a_1914_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1875_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1875_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v___x_1872_);
lean_dec(v_a_1869_);
v_a_1922_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1873_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1873_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_env_1862_);
v_a_1930_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1868_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1868_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_replay___boxed(lean_object* v_newConstants_1945_, lean_object* v_env_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Kernel_Environment_replay(v_newConstants_1945_, v_env_1946_);
lean_dec_ref(v_newConstants_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(lean_object* v_as_1949_, lean_object* v_as_x27_1950_, lean_object* v_b_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___redArg(v_as_x27_1950_, v_b_1951_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0___boxed(lean_object* v_as_1955_, lean_object* v_as_x27_1956_, lean_object* v_b_1957_, lean_object* v_a_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_List_forIn_x27_loop___at___00Lean_Kernel_Environment_replay_spec__0(v_as_1955_, v_as_x27_1956_, v_b_1957_, v_a_1958_);
lean_dec(v_as_x27_1956_);
lean_dec(v_as_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object* v_newConstants_1961_, lean_object* v_env_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_elab_environment_to_kernel_env(v_env_1962_);
v___x_1965_ = l_Lean_Kernel_Environment_replay(v_newConstants_1961_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = l_Lean_Environment_ofKernelEnv(v_a_1966_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1965_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1965_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay___boxed(lean_object* v_newConstants_1983_, lean_object* v_env_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Environment_replay(v_newConstants_1983_, v_env_1984_);
lean_dec_ref(v_newConstants_1983_);
return v_res_1986_;
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
