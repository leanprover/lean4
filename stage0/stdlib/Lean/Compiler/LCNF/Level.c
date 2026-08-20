// Lean compiler output
// Module: Lean.Compiler.LCNF.Level
// Imports: public import Lean.Util.CollectLevelParams public import Lean.Compiler.LCNF.Basic
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Level"};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Compiler.LCNF.NormLevelParam.normLevel"};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Compiler.LCNF.NormLevelParam.normExpr"};
static const lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_normLevelParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_normLevelParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__1;
static const lean_array_object l_Lean_Compiler_LCNF_normLevelParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_normLevelParams___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_normLevelParams___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(lean_object* v_msg_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_2967__overap_32_; lean_object* v___x_33_; 
v___f_10_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_11_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_12_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_13_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_14_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_15_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_16_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___f_10_);
lean_ctor_set(v___x_17_, 1, v___f_11_);
v___x_18_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___f_12_);
lean_ctor_set(v___x_18_, 2, v___f_13_);
lean_ctor_set(v___x_18_, 3, v___f_14_);
lean_ctor_set(v___x_18_, 4, v___f_15_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___f_16_);
lean_inc_ref_n(v___x_19_, 6);
v___f_20_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_20_, 0, v___x_19_);
v___f_21_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_21_, 0, v___x_19_);
v___f_22_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_22_, 0, v___x_19_);
v___f_23_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_23_, 0, v___x_19_);
v___x_24_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_24_, 0, lean_box(0));
lean_closure_set(v___x_24_, 1, lean_box(0));
lean_closure_set(v___x_24_, 2, v___x_19_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___f_20_);
v___x_26_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_26_, 0, lean_box(0));
lean_closure_set(v___x_26_, 1, lean_box(0));
lean_closure_set(v___x_26_, 2, v___x_19_);
v___x_27_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_27_, 0, v___x_25_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
lean_ctor_set(v___x_27_, 2, v___f_21_);
lean_ctor_set(v___x_27_, 3, v___f_22_);
lean_ctor_set(v___x_27_, 4, v___f_23_);
v___x_28_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_28_, 0, lean_box(0));
lean_closure_set(v___x_28_, 1, lean_box(0));
lean_closure_set(v___x_28_, 2, v___x_19_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_box(0);
v___x_31_ = l_instInhabitedOfMonad___redArg(v___x_29_, v___x_30_);
v___x_2967__overap_32_ = lean_panic_fn_borrowed(v___x_31_, v_msg_8_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v___x_2967__overap_32_, v___y_9_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(lean_object* v_a_34_, lean_object* v_b_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_dec(v_b_35_);
lean_dec(v_a_34_);
return v_x_36_;
}
else
{
lean_object* v_key_37_; lean_object* v_value_38_; lean_object* v_tail_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_51_; 
v_key_37_ = lean_ctor_get(v_x_36_, 0);
v_value_38_ = lean_ctor_get(v_x_36_, 1);
v_tail_39_ = lean_ctor_get(v_x_36_, 2);
v_isSharedCheck_51_ = !lean_is_exclusive(v_x_36_);
if (v_isSharedCheck_51_ == 0)
{
v___x_41_ = v_x_36_;
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_tail_39_);
lean_inc(v_value_38_);
lean_inc(v_key_37_);
lean_dec(v_x_36_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_51_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
uint8_t v___x_43_; 
v___x_43_ = lean_name_eq(v_key_37_, v_a_34_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_34_, v_b_35_, v_tail_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 2, v___x_44_);
v___x_46_ = v___x_41_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_key_37_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_value_38_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
else
{
lean_object* v___x_49_; 
lean_dec(v_value_38_);
lean_dec(v_key_37_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 1, v_b_35_);
lean_ctor_set(v___x_41_, 0, v_a_34_);
v___x_49_ = v___x_41_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_34_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v_b_35_);
lean_ctor_set(v_reuseFailAlloc_50_, 2, v_tail_39_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
return v_x_52_;
}
else
{
lean_object* v_key_54_; lean_object* v_value_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_82_; 
v_key_54_ = lean_ctor_get(v_x_53_, 0);
v_value_55_ = lean_ctor_get(v_x_53_, 1);
v_tail_56_ = lean_ctor_get(v_x_53_, 2);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_82_ == 0)
{
v___x_58_ = v_x_53_;
v_isShared_59_ = v_isSharedCheck_82_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_value_55_);
lean_inc(v_key_54_);
lean_dec(v_x_53_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_82_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; uint64_t v___y_62_; 
v___x_60_ = lean_array_get_size(v_x_52_);
if (lean_obj_tag(v_key_54_) == 0)
{
uint64_t v___x_80_; 
v___x_80_ = 1723ULL;
v___y_62_ = v___x_80_;
goto v___jp_61_;
}
else
{
uint64_t v_hash_81_; 
v_hash_81_ = lean_ctor_get_uint64(v_key_54_, sizeof(void*)*2);
v___y_62_ = v_hash_81_;
goto v___jp_61_;
}
v___jp_61_:
{
uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___y_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___y_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_60_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_array_uget_borrowed(v_x_52_, v___x_73_);
lean_inc(v___x_74_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 2, v___x_74_);
v___x_76_ = v___x_58_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_key_54_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_value_55_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v___x_74_);
v___x_76_ = v_reuseFailAlloc_79_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; 
v___x_77_ = lean_array_uset(v_x_52_, v___x_73_, v___x_76_);
v_x_52_ = v___x_77_;
v_x_53_ = v_tail_56_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(lean_object* v_i_83_, lean_object* v_source_84_, lean_object* v_target_85_){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_array_get_size(v_source_84_);
v___x_87_ = lean_nat_dec_lt(v_i_83_, v___x_86_);
if (v___x_87_ == 0)
{
lean_dec_ref(v_source_84_);
lean_dec(v_i_83_);
return v_target_85_;
}
else
{
lean_object* v_es_88_; lean_object* v___x_89_; lean_object* v_source_90_; lean_object* v_target_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_es_88_ = lean_array_fget(v_source_84_, v_i_83_);
v___x_89_ = lean_box(0);
v_source_90_ = lean_array_fset(v_source_84_, v_i_83_, v___x_89_);
v_target_91_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_target_85_, v_es_88_);
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = lean_nat_add(v_i_83_, v___x_92_);
lean_dec(v_i_83_);
v_i_83_ = v___x_93_;
v_source_84_ = v_source_90_;
v_target_85_ = v_target_91_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(lean_object* v_data_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_nbuckets_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = lean_array_get_size(v_data_95_);
v___x_97_ = lean_unsigned_to_nat(2u);
v_nbuckets_98_ = lean_nat_mul(v___x_96_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_box(0);
v___x_101_ = lean_mk_array(v_nbuckets_98_, v___x_100_);
v___x_102_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v___x_99_, v_data_95_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object* v_a_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
else
{
lean_object* v_key_106_; lean_object* v_tail_107_; uint8_t v___x_108_; 
v_key_106_ = lean_ctor_get(v_x_104_, 0);
v_tail_107_ = lean_ctor_get(v_x_104_, 2);
v___x_108_ = lean_name_eq(v_key_106_, v_a_103_);
if (v___x_108_ == 0)
{
v_x_104_ = v_tail_107_;
goto _start;
}
else
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object* v_a_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec(v_a_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object* v_m_114_, lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
lean_object* v_size_117_; lean_object* v_buckets_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_164_; 
v_size_117_ = lean_ctor_get(v_m_114_, 0);
v_buckets_118_ = lean_ctor_get(v_m_114_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_m_114_);
if (v_isSharedCheck_164_ == 0)
{
v___x_120_ = v_m_114_;
v_isShared_121_ = v_isSharedCheck_164_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_buckets_118_);
lean_inc(v_size_117_);
lean_dec(v_m_114_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_164_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; uint64_t v___y_124_; 
v___x_122_ = lean_array_get_size(v_buckets_118_);
if (lean_obj_tag(v_a_115_) == 0)
{
uint64_t v___x_162_; 
v___x_162_ = 1723ULL;
v___y_124_ = v___x_162_;
goto v___jp_123_;
}
else
{
uint64_t v_hash_163_; 
v_hash_163_ = lean_ctor_get_uint64(v_a_115_, sizeof(void*)*2);
v___y_124_ = v_hash_163_;
goto v___jp_123_;
}
v___jp_123_:
{
uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v_fold_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; lean_object* v_bkt_136_; uint8_t v___x_137_; 
v___x_125_ = 32ULL;
v___x_126_ = lean_uint64_shift_right(v___y_124_, v___x_125_);
v_fold_127_ = lean_uint64_xor(v___y_124_, v___x_126_);
v___x_128_ = 16ULL;
v___x_129_ = lean_uint64_shift_right(v_fold_127_, v___x_128_);
v___x_130_ = lean_uint64_xor(v_fold_127_, v___x_129_);
v___x_131_ = lean_uint64_to_usize(v___x_130_);
v___x_132_ = lean_usize_of_nat(v___x_122_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_sub(v___x_132_, v___x_133_);
v___x_135_ = lean_usize_land(v___x_131_, v___x_134_);
v_bkt_136_ = lean_array_uget_borrowed(v_buckets_118_, v___x_135_);
v___x_137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_115_, v_bkt_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v_size_x27_139_; lean_object* v___x_140_; lean_object* v_buckets_x27_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v_size_x27_139_ = lean_nat_add(v_size_117_, v___x_138_);
lean_dec(v_size_117_);
lean_inc(v_bkt_136_);
v___x_140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_140_, 0, v_a_115_);
lean_ctor_set(v___x_140_, 1, v_b_116_);
lean_ctor_set(v___x_140_, 2, v_bkt_136_);
v_buckets_x27_141_ = lean_array_uset(v_buckets_118_, v___x_135_, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(4u);
v___x_143_ = lean_nat_mul(v_size_x27_139_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(3u);
v___x_145_ = lean_nat_div(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_array_get_size(v_buckets_x27_141_);
v___x_147_ = lean_nat_dec_le(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
if (v___x_147_ == 0)
{
lean_object* v_val_148_; lean_object* v___x_150_; 
v_val_148_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_buckets_x27_141_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_val_148_);
lean_ctor_set(v___x_120_, 0, v_size_x27_139_);
v___x_150_ = v___x_120_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_size_x27_139_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_val_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_object* v___x_153_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_buckets_x27_141_);
lean_ctor_set(v___x_120_, 0, v_size_x27_139_);
v___x_153_ = v___x_120_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_size_x27_139_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_buckets_x27_141_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v___x_155_; lean_object* v_buckets_x27_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
lean_inc(v_bkt_136_);
v___x_155_ = lean_box(0);
v_buckets_x27_156_ = lean_array_uset(v_buckets_118_, v___x_135_, v___x_155_);
v___x_157_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_115_, v_b_116_, v_bkt_136_);
v___x_158_ = lean_array_uset(v_buckets_x27_156_, v___x_135_, v___x_157_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_158_);
v___x_160_ = v___x_120_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_117_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_key_168_; lean_object* v_value_169_; lean_object* v_tail_170_; uint8_t v___x_171_; 
v_key_168_ = lean_ctor_get(v_x_166_, 0);
v_value_169_ = lean_ctor_get(v_x_166_, 1);
v_tail_170_ = lean_ctor_get(v_x_166_, 2);
v___x_171_ = lean_name_eq(v_key_168_, v_a_165_);
if (v___x_171_ == 0)
{
v_x_166_ = v_tail_170_;
goto _start;
}
else
{
lean_object* v___x_173_; 
lean_inc(v_value_169_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_value_169_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_buckets_179_; lean_object* v___x_180_; uint64_t v___y_182_; 
v_buckets_179_ = lean_ctor_get(v_m_177_, 1);
v___x_180_ = lean_array_get_size(v_buckets_179_);
if (lean_obj_tag(v_a_178_) == 0)
{
uint64_t v___x_196_; 
v___x_196_ = 1723ULL;
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
else
{
uint64_t v_hash_197_; 
v_hash_197_ = lean_ctor_get_uint64(v_a_178_, sizeof(void*)*2);
v___y_182_ = v_hash_197_;
goto v___jp_181_;
}
v___jp_181_:
{
uint64_t v___x_183_; uint64_t v___x_184_; uint64_t v_fold_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_183_ = 32ULL;
v___x_184_ = lean_uint64_shift_right(v___y_182_, v___x_183_);
v_fold_185_ = lean_uint64_xor(v___y_182_, v___x_184_);
v___x_186_ = 16ULL;
v___x_187_ = lean_uint64_shift_right(v_fold_185_, v___x_186_);
v___x_188_ = lean_uint64_xor(v_fold_185_, v___x_187_);
v___x_189_ = lean_uint64_to_usize(v___x_188_);
v___x_190_ = lean_usize_of_nat(v___x_180_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_sub(v___x_190_, v___x_191_);
v___x_193_ = lean_usize_land(v___x_189_, v___x_192_);
v___x_194_ = lean_array_uget_borrowed(v_buckets_179_, v___x_193_);
v___x_195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_178_, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg___boxed(lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_m_198_);
return v_res_200_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_207_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_208_ = lean_unsigned_to_nat(19u);
v___x_209_ = lean_unsigned_to_nat(55u);
v___x_210_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3));
v___x_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_212_ = l_mkPanicMessageWithDecl(v___x_211_, v___x_210_, v___x_209_, v___x_208_, v___x_207_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel(lean_object* v_u_213_, lean_object* v_a_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Level_hasParam(v_u_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_u_213_);
lean_ctor_set(v___x_216_, 1, v_a_214_);
return v___x_216_;
}
else
{
switch(lean_obj_tag(v_u_213_))
{
case 0:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_u_213_);
lean_ctor_set(v___x_217_, 1, v_a_214_);
return v___x_217_;
}
case 1:
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_235_; 
v_a_218_ = lean_ctor_get(v_u_213_, 0);
lean_inc(v_a_218_);
v___x_219_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_218_, v_a_214_);
v_fst_220_ = lean_ctor_get(v___x_219_, 0);
v_snd_221_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_235_ == 0)
{
v___x_223_ = v___x_219_;
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snd_221_);
lean_inc(v_fst_220_);
lean_dec(v___x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
size_t v___x_225_; size_t v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_ptr_addr(v_a_218_);
v___x_226_ = lean_ptr_addr(v_fst_220_);
v___x_227_ = lean_usize_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_230_; 
lean_dec_ref_known(v_u_213_, 1);
v___x_228_ = l_Lean_Level_succ___override(v_fst_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_228_);
v___x_230_ = v___x_223_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_snd_221_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
else
{
lean_object* v___x_233_; 
lean_dec(v_fst_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v_u_213_);
v___x_233_ = v___x_223_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_u_213_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_snd_221_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
case 2:
{
lean_object* v_a_236_; lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_265_; 
v_a_236_ = lean_ctor_get(v_u_213_, 0);
v_a_237_ = lean_ctor_get(v_u_213_, 1);
lean_inc(v_a_236_);
v___x_238_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_236_, v_a_214_);
v_fst_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_fst_239_);
v_snd_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_snd_240_);
lean_dec_ref(v___x_238_);
lean_inc(v_a_237_);
v___x_241_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_237_, v_snd_240_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
v_snd_243_ = lean_ctor_get(v___x_241_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_265_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_265_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
size_t v___x_247_; size_t v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_ptr_addr(v_a_236_);
v___x_248_ = lean_ptr_addr(v_fst_239_);
v___x_249_ = lean_usize_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_250_ = l_Lean_mkLevelMax_x27(v_fst_239_, v_fst_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_250_);
v___x_252_ = v___x_245_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_243_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
size_t v___x_254_; size_t v___x_255_; uint8_t v___x_256_; 
v___x_254_ = lean_ptr_addr(v_a_237_);
v___x_255_ = lean_ptr_addr(v_fst_242_);
v___x_256_ = lean_usize_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_257_ = l_Lean_mkLevelMax_x27(v_fst_239_, v_fst_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_257_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_243_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_simpLevelMax_x27(v_fst_239_, v_fst_242_, v_u_213_);
lean_dec_ref_known(v_u_213_, 2);
lean_dec(v_fst_242_);
lean_dec(v_fst_239_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_261_);
v___x_263_ = v___x_245_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_snd_243_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
case 3:
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_295_; 
v_a_266_ = lean_ctor_get(v_u_213_, 0);
v_a_267_ = lean_ctor_get(v_u_213_, 1);
lean_inc(v_a_266_);
v___x_268_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_266_, v_a_214_);
v_fst_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_fst_269_);
v_snd_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v___x_268_);
lean_inc(v_a_267_);
v___x_271_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_267_, v_snd_270_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
v_snd_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_295_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_295_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snd_273_);
lean_inc(v_fst_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_295_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
size_t v___x_277_; size_t v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_ptr_addr(v_a_266_);
v___x_278_ = lean_ptr_addr(v_fst_269_);
v___x_279_ = lean_usize_dec_eq(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_280_ = l_Lean_mkLevelIMax_x27(v_fst_269_, v_fst_272_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_280_);
v___x_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_snd_273_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
else
{
size_t v___x_284_; size_t v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_ptr_addr(v_a_267_);
v___x_285_ = lean_ptr_addr(v_fst_272_);
v___x_286_ = lean_usize_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_287_ = l_Lean_mkLevelIMax_x27(v_fst_269_, v_fst_272_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_287_);
v___x_289_ = v___x_275_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_snd_273_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_simpLevelIMax_x27(v_fst_269_, v_fst_272_, v_u_213_);
lean_dec_ref_known(v_u_213_, 2);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_291_);
v___x_293_ = v___x_275_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_snd_273_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
case 4:
{
lean_object* v_a_296_; lean_object* v_nextIdx_297_; lean_object* v_map_298_; lean_object* v_paramNames_299_; lean_object* v___x_300_; 
v_a_296_ = lean_ctor_get(v_u_213_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v_u_213_, 1);
v_nextIdx_297_ = lean_ctor_get(v_a_214_, 0);
v_map_298_ = lean_ctor_get(v_a_214_, 1);
v_paramNames_299_ = lean_ctor_get(v_a_214_, 2);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_298_, v_a_296_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_315_; 
lean_inc_ref(v_paramNames_299_);
lean_inc_ref(v_map_298_);
lean_inc(v_nextIdx_297_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_316_ = lean_ctor_get(v_a_214_, 2);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_a_214_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_318_);
v___x_302_ = v_a_214_;
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_a_214_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_304_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_297_);
v___x_305_ = lean_name_append_index_after(v___x_304_, v_nextIdx_297_);
v___x_306_ = l_Lean_Level_param___override(v___x_305_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_nextIdx_297_, v___x_307_);
lean_dec(v_nextIdx_297_);
lean_inc(v___x_306_);
lean_inc(v_a_296_);
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_298_, v_a_296_, v___x_306_);
v___x_310_ = lean_array_push(v_paramNames_299_, v_a_296_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 2, v___x_310_);
lean_ctor_set(v___x_302_, 1, v___x_309_);
lean_ctor_set(v___x_302_, 0, v___x_308_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v___x_310_);
v___x_312_ = v_reuseFailAlloc_314_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_306_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
return v___x_313_;
}
}
}
else
{
lean_object* v_val_319_; lean_object* v___x_320_; 
lean_dec(v_a_296_);
v_val_319_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_val_319_);
lean_dec_ref_known(v___x_300_, 1);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_val_319_);
lean_ctor_set(v___x_320_, 1, v_a_214_);
return v___x_320_;
}
}
default: 
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref_known(v_u_213_, 1);
v___x_321_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_322_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_321_, v_a_214_);
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_324_, v_a_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_327_, v_m_328_, v_a_329_);
lean_dec(v_a_329_);
lean_dec_ref(v_m_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_331_, lean_object* v_m_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_332_, v_a_333_, v_b_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_340_, v_a_341_, v_x_342_);
lean_dec(v_x_342_);
lean_dec(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_344_, lean_object* v_a_345_, lean_object* v_x_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_348_, lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_348_, v_a_349_, v_x_350_);
lean_dec(v_x_350_);
lean_dec(v_a_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_353_, lean_object* v_data_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_356_, lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_x_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_357_, v_b_358_, v_x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_361_, lean_object* v_i_362_, lean_object* v_source_363_, lean_object* v_target_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_362_, v_source_363_, v_target_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_367_, v_x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_4908__overap_394_; lean_object* v___x_395_; 
v___f_372_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___f_372_);
lean_ctor_set(v___x_379_, 1, v___f_373_);
v___x_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___f_374_);
lean_ctor_set(v___x_380_, 2, v___f_375_);
lean_ctor_set(v___x_380_, 3, v___f_376_);
lean_ctor_set(v___x_380_, 4, v___f_377_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___f_378_);
lean_inc_ref_n(v___x_381_, 6);
v___f_382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_382_, 0, v___x_381_);
v___f_383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_383_, 0, v___x_381_);
v___f_384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_384_, 0, v___x_381_);
v___f_385_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_385_, 0, v___x_381_);
v___x_386_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_386_, 0, lean_box(0));
lean_closure_set(v___x_386_, 1, lean_box(0));
lean_closure_set(v___x_386_, 2, v___x_381_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___f_382_);
v___x_388_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_388_, 0, lean_box(0));
lean_closure_set(v___x_388_, 1, lean_box(0));
lean_closure_set(v___x_388_, 2, v___x_381_);
v___x_389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
lean_ctor_set(v___x_389_, 2, v___f_383_);
lean_ctor_set(v___x_389_, 3, v___f_384_);
lean_ctor_set(v___x_389_, 4, v___f_385_);
v___x_390_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_390_, 0, lean_box(0));
lean_closure_set(v___x_390_, 1, lean_box(0));
lean_closure_set(v___x_390_, 2, v___x_381_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_instInhabitedExpr;
v___x_393_ = l_instInhabitedOfMonad___redArg(v___x_391_, v___x_392_);
v___x_4908__overap_394_ = lean_panic_fn_borrowed(v___x_393_, v_msg_370_);
lean_dec(v___x_393_);
v___x_395_ = lean_apply_1(v___x_4908__overap_394_, v___y_371_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v___y_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = l_List_reverse___redArg(v_x_397_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___y_398_);
return v___x_400_;
}
else
{
lean_object* v_head_401_; lean_object* v_tail_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_413_; 
v_head_401_ = lean_ctor_get(v_x_396_, 0);
v_tail_402_ = lean_ctor_get(v_x_396_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_396_);
if (v_isSharedCheck_413_ == 0)
{
v___x_404_ = v_x_396_;
v_isShared_405_ = v_isSharedCheck_413_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_tail_402_);
lean_inc(v_head_401_);
lean_dec(v_x_396_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_413_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; 
v___x_406_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_401_, v___y_398_);
v_fst_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v___x_406_, 1);
lean_inc(v_snd_408_);
lean_dec_ref(v___x_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v_x_397_);
lean_ctor_set(v___x_404_, 0, v_fst_407_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fst_407_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_x_397_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v_x_396_ = v_tail_402_;
v_x_397_ = v___x_410_;
v___y_398_ = v_snd_408_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_416_ = lean_unsigned_to_nat(26u);
v___x_417_ = lean_unsigned_to_nat(79u);
v___x_418_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_419_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_420_ = l_mkPanicMessageWithDecl(v___x_419_, v___x_418_, v___x_417_, v___x_416_, v___x_415_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_421_, lean_object* v_a_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l_Lean_Expr_hasLevelParam(v_e_421_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_e_421_);
lean_ctor_set(v___x_424_, 1, v_a_422_);
return v___x_424_;
}
else
{
switch(lean_obj_tag(v_e_421_))
{
case 4:
{
lean_object* v_declName_425_; lean_object* v_us_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_442_; 
v_declName_425_ = lean_ctor_get(v_e_421_, 0);
v_us_426_ = lean_ctor_get(v_e_421_, 1);
v___x_427_ = lean_box(0);
lean_inc(v_us_426_);
v___x_428_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_426_, v___x_427_, v_a_422_);
v_fst_429_ = lean_ctor_get(v___x_428_, 0);
v_snd_430_ = lean_ctor_get(v___x_428_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_442_ == 0)
{
v___x_432_ = v___x_428_;
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snd_430_);
lean_inc(v_fst_429_);
lean_dec(v___x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; 
v___x_434_ = l_ptrEqList___redArg(v_us_426_, v_fst_429_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc(v_declName_425_);
lean_dec_ref_known(v_e_421_, 2);
v___x_435_ = l_Lean_Expr_const___override(v_declName_425_, v_fst_429_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_snd_430_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v___x_440_; 
lean_dec(v_fst_429_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_e_421_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
case 3:
{
lean_object* v_u_443_; lean_object* v___x_444_; lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_460_; 
v_u_443_ = lean_ctor_get(v_e_421_, 0);
lean_inc(v_u_443_);
v___x_444_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_443_, v_a_422_);
v_fst_445_ = lean_ctor_get(v___x_444_, 0);
v_snd_446_ = lean_ctor_get(v___x_444_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_460_ == 0)
{
v___x_448_ = v___x_444_;
v_isShared_449_ = v_isSharedCheck_460_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_snd_446_);
lean_inc(v_fst_445_);
lean_dec(v___x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_460_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_ptr_addr(v_u_443_);
v___x_451_ = lean_ptr_addr(v_fst_445_);
v___x_452_ = lean_usize_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec_ref_known(v_e_421_, 1);
v___x_453_ = l_Lean_Expr_sort___override(v_fst_445_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_453_);
v___x_455_ = v___x_448_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_snd_446_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec(v_fst_445_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v_e_421_);
v___x_458_ = v___x_448_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_snd_446_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
case 5:
{
lean_object* v_fn_461_; lean_object* v_arg_462_; lean_object* v___x_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_489_; 
v_fn_461_ = lean_ctor_get(v_e_421_, 0);
v_arg_462_ = lean_ctor_get(v_e_421_, 1);
lean_inc_ref(v_fn_461_);
v___x_463_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_461_, v_a_422_);
v_fst_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___x_463_);
lean_inc_ref(v_arg_462_);
v___x_466_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_462_, v_snd_465_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_489_ == 0)
{
v___x_470_ = v___x_466_;
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snd_468_);
lean_inc(v_fst_467_);
lean_dec(v___x_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_489_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_ptr_addr(v_fn_461_);
v___x_473_ = lean_ptr_addr(v_fst_464_);
v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec_ref_known(v_e_421_, 2);
v___x_475_ = l_Lean_Expr_app___override(v_fst_464_, v_fst_467_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_475_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_468_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
size_t v___x_479_; size_t v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_ptr_addr(v_arg_462_);
v___x_480_ = lean_ptr_addr(v_fst_467_);
v___x_481_ = lean_usize_dec_eq(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec_ref_known(v_e_421_, 2);
v___x_482_ = l_Lean_Expr_app___override(v_fst_464_, v_fst_467_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_482_);
v___x_484_ = v___x_470_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_snd_468_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_fst_467_);
lean_dec(v_fst_464_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v_e_421_);
v___x_487_ = v___x_470_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_468_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_490_; lean_object* v_type_491_; lean_object* v_value_492_; lean_object* v_body_493_; uint8_t v_nondep_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_531_; 
v_declName_490_ = lean_ctor_get(v_e_421_, 0);
v_type_491_ = lean_ctor_get(v_e_421_, 1);
v_value_492_ = lean_ctor_get(v_e_421_, 2);
v_body_493_ = lean_ctor_get(v_e_421_, 3);
v_nondep_494_ = lean_ctor_get_uint8(v_e_421_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_491_);
v___x_495_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_491_, v_a_422_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_495_);
lean_inc_ref(v_value_492_);
v___x_498_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_492_, v_snd_497_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_fst_499_);
v_snd_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_snd_500_);
lean_dec_ref(v___x_498_);
lean_inc_ref(v_body_493_);
v___x_501_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_493_, v_snd_500_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
v_snd_503_ = lean_ctor_get(v___x_501_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_531_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_531_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_inc(v_fst_502_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_531_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v___x_507_ = lean_ptr_addr(v_type_491_);
v___x_508_ = lean_ptr_addr(v_fst_496_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v_e_421_, 4);
v___x_510_ = l_Lean_Expr_letE___override(v_declName_490_, v_fst_496_, v_fst_499_, v_fst_502_, v_nondep_494_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_510_);
v___x_512_ = v___x_505_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_snd_503_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_ptr_addr(v_value_492_);
v___x_515_ = lean_ptr_addr(v_fst_499_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v_e_421_, 4);
v___x_517_ = l_Lean_Expr_letE___override(v_declName_490_, v_fst_496_, v_fst_499_, v_fst_502_, v_nondep_494_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_517_);
v___x_519_ = v___x_505_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_503_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v___x_521_ = lean_ptr_addr(v_body_493_);
v___x_522_ = lean_ptr_addr(v_fst_502_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v_e_421_, 4);
v___x_524_ = l_Lean_Expr_letE___override(v_declName_490_, v_fst_496_, v_fst_499_, v_fst_502_, v_nondep_494_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_524_);
v___x_526_ = v___x_505_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_snd_503_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v_fst_502_);
lean_dec(v_fst_499_);
lean_dec(v_fst_496_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_e_421_);
v___x_529_ = v___x_505_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_503_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_532_; lean_object* v_binderType_533_; lean_object* v_body_534_; uint8_t v_binderInfo_535_; lean_object* v___x_536_; lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_567_; 
v_binderName_532_ = lean_ctor_get(v_e_421_, 0);
v_binderType_533_ = lean_ctor_get(v_e_421_, 1);
v_body_534_ = lean_ctor_get(v_e_421_, 2);
v_binderInfo_535_ = lean_ctor_get_uint8(v_e_421_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_533_);
v___x_536_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_533_, v_a_422_);
v_fst_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_fst_537_);
v_snd_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc(v_snd_538_);
lean_dec_ref(v___x_536_);
lean_inc_ref(v_body_534_);
v___x_539_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_534_, v_snd_538_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_567_ == 0)
{
v___x_543_ = v___x_539_;
v_isShared_544_ = v_isSharedCheck_567_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_inc(v_fst_540_);
lean_dec(v___x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_567_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
size_t v___x_545_; size_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_ptr_addr(v_binderType_533_);
v___x_546_ = lean_ptr_addr(v_fst_537_);
v___x_547_ = lean_usize_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_inc(v_binderName_532_);
lean_dec_ref_known(v_e_421_, 3);
v___x_548_ = l_Lean_Expr_forallE___override(v_binderName_532_, v_fst_537_, v_fst_540_, v_binderInfo_535_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_548_);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_snd_541_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_ptr_addr(v_body_534_);
v___x_553_ = lean_ptr_addr(v_fst_540_);
v___x_554_ = lean_usize_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_inc(v_binderName_532_);
lean_dec_ref_known(v_e_421_, 3);
v___x_555_ = l_Lean_Expr_forallE___override(v_binderName_532_, v_fst_537_, v_fst_540_, v_binderInfo_535_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_555_);
v___x_557_ = v___x_543_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_snd_541_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
uint8_t v___x_559_; 
v___x_559_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_535_, v_binderInfo_535_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_inc(v_binderName_532_);
lean_dec_ref_known(v_e_421_, 3);
v___x_560_ = l_Lean_Expr_forallE___override(v_binderName_532_, v_fst_537_, v_fst_540_, v_binderInfo_535_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_560_);
v___x_562_ = v___x_543_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_snd_541_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v___x_565_; 
lean_dec(v_fst_540_);
lean_dec(v_fst_537_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_e_421_);
v___x_565_ = v___x_543_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_541_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_568_; lean_object* v_binderType_569_; lean_object* v_body_570_; uint8_t v_binderInfo_571_; lean_object* v___x_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_603_; 
v_binderName_568_ = lean_ctor_get(v_e_421_, 0);
v_binderType_569_ = lean_ctor_get(v_e_421_, 1);
v_body_570_ = lean_ctor_get(v_e_421_, 2);
v_binderInfo_571_ = lean_ctor_get_uint8(v_e_421_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_569_);
v___x_572_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_569_, v_a_422_);
v_fst_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v___x_572_);
lean_inc_ref(v_body_570_);
v___x_575_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_570_, v_snd_574_);
v_fst_576_ = lean_ctor_get(v___x_575_, 0);
v_snd_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_603_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_603_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_603_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
size_t v___x_581_; size_t v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_ptr_addr(v_binderType_569_);
v___x_582_ = lean_ptr_addr(v_fst_573_);
v___x_583_ = lean_usize_dec_eq(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_586_; 
lean_inc(v_binderName_568_);
lean_dec_ref_known(v_e_421_, 3);
v___x_584_ = l_Lean_Expr_lam___override(v_binderName_568_, v_fst_573_, v_fst_576_, v_binderInfo_571_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_577_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
size_t v___x_588_; size_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_ptr_addr(v_body_570_);
v___x_589_ = lean_ptr_addr(v_fst_576_);
v___x_590_ = lean_usize_dec_eq(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_inc(v_binderName_568_);
lean_dec_ref_known(v_e_421_, 3);
v___x_591_ = l_Lean_Expr_lam___override(v_binderName_568_, v_fst_573_, v_fst_576_, v_binderInfo_571_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_591_);
v___x_593_ = v___x_579_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_577_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_571_, v_binderInfo_571_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_inc(v_binderName_568_);
lean_dec_ref_known(v_e_421_, 3);
v___x_596_ = l_Lean_Expr_lam___override(v_binderName_568_, v_fst_573_, v_fst_576_, v_binderInfo_571_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_596_);
v___x_598_ = v___x_579_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_snd_577_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_601_; 
lean_dec(v_fst_576_);
lean_dec(v_fst_573_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v_e_421_);
v___x_601_ = v___x_579_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_577_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_604_; lean_object* v_expr_605_; lean_object* v___x_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_622_; 
v_data_604_ = lean_ctor_get(v_e_421_, 0);
v_expr_605_ = lean_ctor_get(v_e_421_, 1);
lean_inc_ref(v_expr_605_);
v___x_606_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_605_, v_a_422_);
v_fst_607_ = lean_ctor_get(v___x_606_, 0);
v_snd_608_ = lean_ctor_get(v___x_606_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_622_ == 0)
{
v___x_610_ = v___x_606_;
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snd_608_);
lean_inc(v_fst_607_);
lean_dec(v___x_606_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_622_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
size_t v___x_612_; size_t v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_ptr_addr(v_expr_605_);
v___x_613_ = lean_ptr_addr(v_fst_607_);
v___x_614_ = lean_usize_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_617_; 
lean_inc(v_data_604_);
lean_dec_ref_known(v_e_421_, 2);
v___x_615_ = l_Lean_Expr_mdata___override(v_data_604_, v_fst_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_615_);
v___x_617_ = v___x_610_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_608_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_object* v___x_620_; 
lean_dec(v_fst_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_e_421_);
v___x_620_ = v___x_610_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_snd_608_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
case 11:
{
lean_object* v_typeName_623_; lean_object* v_idx_624_; lean_object* v_struct_625_; lean_object* v___x_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_642_; 
v_typeName_623_ = lean_ctor_get(v_e_421_, 0);
v_idx_624_ = lean_ctor_get(v_e_421_, 1);
v_struct_625_ = lean_ctor_get(v_e_421_, 2);
lean_inc_ref(v_struct_625_);
v___x_626_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_625_, v_a_422_);
v_fst_627_ = lean_ctor_get(v___x_626_, 0);
v_snd_628_ = lean_ctor_get(v___x_626_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_642_ == 0)
{
v___x_630_ = v___x_626_;
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_inc(v_fst_627_);
lean_dec(v___x_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_642_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_ptr_addr(v_struct_625_);
v___x_633_ = lean_ptr_addr(v_fst_627_);
v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc(v_idx_624_);
lean_inc(v_typeName_623_);
lean_dec_ref_known(v_e_421_, 3);
v___x_635_ = l_Lean_Expr_proj___override(v_typeName_623_, v_idx_624_, v_fst_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_635_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_snd_628_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_fst_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_e_421_);
v___x_640_ = v___x_630_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_e_421_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_snd_628_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
case 2:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref_known(v_e_421_, 1);
v___x_643_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_644_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_643_, v_a_422_);
return v___x_644_;
}
default: 
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_e_421_);
lean_ctor_set(v___x_645_, 1, v_a_422_);
return v___x_645_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_box(0);
v___x_647_ = lean_unsigned_to_nat(16u);
v___x_648_ = lean_mk_array(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_655_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_snd_661_; lean_object* v_fst_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_671_; 
v___x_659_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_660_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_658_, v___x_659_);
v_snd_661_ = lean_ctor_get(v___x_660_, 1);
v_fst_662_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_671_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_662_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_paramNames_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v_paramNames_666_ = lean_ctor_get(v_snd_661_, 2);
lean_inc_ref(v_paramNames_666_);
lean_dec(v_snd_661_);
v___x_667_ = lean_array_to_list(v_paramNames_666_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_662_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_CollectLevelParams_visitExpr(v_type_672_, v_a_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_675_, lean_object* v_a_676_){
_start:
{
if (lean_obj_tag(v_arg_675_) == 2)
{
lean_object* v_expr_677_; lean_object* v___x_678_; 
v_expr_677_ = lean_ctor_get(v_arg_675_, 0);
lean_inc_ref(v_expr_677_);
lean_dec_ref_known(v_arg_675_, 1);
v___x_678_ = l_Lean_CollectLevelParams_visitExpr(v_expr_677_, v_a_676_);
return v___x_678_;
}
else
{
lean_dec(v_arg_675_);
return v_a_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; size_t v___x_686_; size_t v___x_687_; 
v___x_684_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_684_, v_b_682_);
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_680_, v___x_686_);
v_i_680_ = v___x_687_;
v_b_682_ = v___x_685_;
goto _start;
}
else
{
return v_b_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_stop_691_, lean_object* v_b_692_){
_start:
{
size_t v_i_boxed_693_; size_t v_stop_boxed_694_; lean_object* v_res_695_; 
v_i_boxed_693_ = lean_unbox_usize(v_i_690_);
lean_dec(v_i_690_);
v_stop_boxed_694_ = lean_unbox_usize(v_stop_691_);
lean_dec(v_stop_691_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_689_, v_i_boxed_693_, v_stop_boxed_694_, v_b_692_);
lean_dec_ref(v_as_689_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_696_, lean_object* v_s_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_array_get_size(v_args_696_);
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
return v_s_697_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_le(v___x_699_, v___x_699_);
if (v___x_701_ == 0)
{
if (v___x_700_ == 0)
{
return v_s_697_;
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_699_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_696_, v___x_702_, v___x_703_, v_s_697_);
return v___x_704_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_699_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_696_, v___x_705_, v___x_706_, v_s_697_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_708_, lean_object* v_s_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_708_, v_s_709_);
lean_dec_ref(v_args_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_711_, lean_object* v_a_712_){
_start:
{
switch(lean_obj_tag(v_e_711_))
{
case 3:
{
lean_object* v_us_713_; lean_object* v_args_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_us_713_ = lean_ctor_get(v_e_711_, 1);
lean_inc(v_us_713_);
v_args_714_ = lean_ctor_get(v_e_711_, 2);
lean_inc_ref(v_args_714_);
lean_dec_ref_known(v_e_711_, 3);
v___x_715_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_714_, v_a_712_);
lean_dec_ref(v_args_714_);
v___x_716_ = l_Lean_CollectLevelParams_visitLevels(v_us_713_, v___x_715_);
return v___x_716_;
}
case 4:
{
lean_object* v_args_717_; lean_object* v___x_718_; 
v_args_717_ = lean_ctor_get(v_e_711_, 1);
lean_inc_ref(v_args_717_);
lean_dec_ref_known(v_e_711_, 2);
v___x_718_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_717_, v_a_712_);
lean_dec_ref(v_args_717_);
return v___x_718_;
}
default: 
{
lean_dec(v_e_711_);
return v_a_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_type_721_; lean_object* v___x_722_; 
v_type_721_ = lean_ctor_get(v_p_719_, 2);
lean_inc_ref(v_type_721_);
lean_dec_ref(v_p_719_);
v___x_722_ = l_Lean_CollectLevelParams_visitExpr(v_type_721_, v_a_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_723_, size_t v_i_724_, size_t v_stop_725_, lean_object* v_b_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_eq(v_i_724_, v_stop_725_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; 
v___x_728_ = lean_array_uget_borrowed(v_as_723_, v_i_724_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_728_, v_b_726_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_724_, v___x_730_);
v_i_724_ = v___x_731_;
v_b_726_ = v___x_729_;
goto _start;
}
else
{
return v_b_726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_){
_start:
{
size_t v_i_boxed_737_; size_t v_stop_boxed_738_; lean_object* v_res_739_; 
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_738_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_733_, v_i_boxed_737_, v_stop_boxed_738_, v_b_736_);
lean_dec_ref(v_as_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_740_, lean_object* v_s_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_array_get_size(v_ps_740_);
v___x_744_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
return v_s_741_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_le(v___x_743_, v___x_743_);
if (v___x_745_ == 0)
{
if (v___x_744_ == 0)
{
return v_s_741_;
}
else
{
size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v___x_746_ = ((size_t)0ULL);
v___x_747_ = lean_usize_of_nat(v___x_743_);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_740_, v___x_746_, v___x_747_, v_s_741_);
return v___x_748_;
}
}
else
{
size_t v___x_749_; size_t v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((size_t)0ULL);
v___x_750_ = lean_usize_of_nat(v___x_743_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_740_, v___x_749_, v___x_750_, v_s_741_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_752_, lean_object* v_s_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_752_, v_s_753_);
lean_dec_ref(v_ps_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_, lean_object* v_b_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; 
v___x_760_ = lean_array_uget_borrowed(v_as_755_, v_i_756_);
lean_inc(v___x_760_);
v___x_761_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_760_, v_b_758_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_756_, v___x_762_);
v_i_756_ = v___x_763_;
v_b_758_ = v___x_761_;
goto _start;
}
else
{
return v_b_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_765_, lean_object* v_s_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_array_get_size(v_alts_765_);
v___x_769_ = lean_nat_dec_lt(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
return v_s_766_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = lean_nat_dec_le(v___x_768_, v___x_768_);
if (v___x_770_ == 0)
{
if (v___x_769_ == 0)
{
return v_s_766_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_of_nat(v___x_768_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_765_, v___x_771_, v___x_772_, v_s_766_);
return v___x_773_;
}
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_768_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_765_, v___x_774_, v___x_775_, v_s_766_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_777_, lean_object* v_a_778_){
_start:
{
switch(lean_obj_tag(v_x_777_))
{
case 0:
{
lean_object* v_decl_779_; lean_object* v_k_780_; lean_object* v_type_781_; lean_object* v_value_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_decl_779_ = lean_ctor_get(v_x_777_, 0);
lean_inc_ref(v_decl_779_);
v_k_780_ = lean_ctor_get(v_x_777_, 1);
lean_inc_ref(v_k_780_);
lean_dec_ref_known(v_x_777_, 2);
v_type_781_ = lean_ctor_get(v_decl_779_, 2);
lean_inc_ref(v_type_781_);
v_value_782_ = lean_ctor_get(v_decl_779_, 3);
lean_inc(v_value_782_);
lean_dec_ref(v_decl_779_);
v___x_783_ = l_Lean_CollectLevelParams_visitExpr(v_type_781_, v_a_778_);
v___x_784_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_782_, v___x_783_);
v_x_777_ = v_k_780_;
v_a_778_ = v___x_784_;
goto _start;
}
case 3:
{
lean_object* v_args_786_; lean_object* v___x_787_; 
v_args_786_ = lean_ctor_get(v_x_777_, 1);
lean_inc_ref(v_args_786_);
lean_dec_ref_known(v_x_777_, 2);
v___x_787_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_786_, v_a_778_);
lean_dec_ref(v_args_786_);
return v___x_787_;
}
case 4:
{
lean_object* v_cases_788_; lean_object* v_resultType_789_; lean_object* v_alts_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_cases_788_ = lean_ctor_get(v_x_777_, 0);
lean_inc_ref(v_cases_788_);
lean_dec_ref_known(v_x_777_, 1);
v_resultType_789_ = lean_ctor_get(v_cases_788_, 1);
lean_inc_ref(v_resultType_789_);
v_alts_790_ = lean_ctor_get(v_cases_788_, 3);
lean_inc_ref(v_alts_790_);
lean_dec_ref(v_cases_788_);
v___x_791_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_789_, v_a_778_);
v___x_792_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_790_, v___x_791_);
lean_dec_ref(v_alts_790_);
return v___x_792_;
}
case 5:
{
lean_dec_ref_known(v_x_777_, 1);
return v_a_778_;
}
case 6:
{
lean_object* v_type_793_; lean_object* v___x_794_; 
v_type_793_ = lean_ctor_get(v_x_777_, 0);
lean_inc_ref(v_type_793_);
lean_dec_ref_known(v_x_777_, 1);
v___x_794_ = l_Lean_CollectLevelParams_visitExpr(v_type_793_, v_a_778_);
return v___x_794_;
}
default: 
{
lean_object* v_decl_795_; lean_object* v_k_796_; lean_object* v_params_797_; lean_object* v_type_798_; lean_object* v_value_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_decl_795_ = lean_ctor_get(v_x_777_, 0);
lean_inc_ref(v_decl_795_);
v_k_796_ = lean_ctor_get(v_x_777_, 1);
lean_inc_ref(v_k_796_);
lean_dec_ref(v_x_777_);
v_params_797_ = lean_ctor_get(v_decl_795_, 2);
lean_inc_ref(v_params_797_);
v_type_798_ = lean_ctor_get(v_decl_795_, 3);
lean_inc_ref(v_type_798_);
v_value_799_ = lean_ctor_get(v_decl_795_, 4);
lean_inc_ref(v_value_799_);
lean_dec_ref(v_decl_795_);
v___x_800_ = l_Lean_CollectLevelParams_visitExpr(v_type_798_, v_a_778_);
v___x_801_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_797_, v___x_800_);
lean_dec_ref(v_params_797_);
v___x_802_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_799_, v___x_801_);
v_x_777_ = v_k_796_;
v_a_778_ = v___x_802_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_804_, lean_object* v_a_805_){
_start:
{
if (lean_obj_tag(v_alt_804_) == 0)
{
lean_object* v_params_806_; lean_object* v_code_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_params_806_ = lean_ctor_get(v_alt_804_, 1);
lean_inc_ref(v_params_806_);
v_code_807_ = lean_ctor_get(v_alt_804_, 2);
lean_inc_ref(v_code_807_);
lean_dec_ref_known(v_alt_804_, 3);
v___x_808_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_806_, v_a_805_);
lean_dec_ref(v_params_806_);
v___x_809_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_807_, v___x_808_);
return v___x_809_;
}
else
{
lean_object* v_code_810_; lean_object* v___x_811_; 
v_code_810_ = lean_ctor_get(v_alt_804_, 0);
lean_inc_ref(v_code_810_);
lean_dec_ref_known(v_alt_804_, 1);
v___x_811_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_810_, v_a_805_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_812_, lean_object* v_i_813_, lean_object* v_stop_814_, lean_object* v_b_815_){
_start:
{
size_t v_i_boxed_816_; size_t v_stop_boxed_817_; lean_object* v_res_818_; 
v_i_boxed_816_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_stop_boxed_817_ = lean_unbox_usize(v_stop_814_);
lean_dec(v_stop_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_812_, v_i_boxed_816_, v_stop_boxed_817_, v_b_815_);
lean_dec_ref(v_as_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_819_, lean_object* v_s_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_819_, v_s_820_);
lean_dec_ref(v_alts_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_822_, lean_object* v_a_823_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_code_824_; lean_object* v___x_825_; 
v_code_824_ = lean_ctor_get(v_x_822_, 0);
lean_inc_ref(v_code_824_);
lean_dec_ref_known(v_x_822_, 1);
v___x_825_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_824_, v_a_823_);
return v___x_825_;
}
else
{
lean_dec_ref_known(v_x_822_, 1);
return v_a_823_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_unsigned_to_nat(16u);
v___x_828_ = lean_mk_array(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_833_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_ctor_set(v___x_834_, 2, v___x_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_835_){
_start:
{
lean_object* v_toSignature_836_; lean_object* v_value_837_; uint8_t v_recursive_838_; lean_object* v_inlineAttr_x3f_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_864_; 
v_toSignature_836_ = lean_ctor_get(v_decl_835_, 0);
v_value_837_ = lean_ctor_get(v_decl_835_, 1);
v_recursive_838_ = lean_ctor_get_uint8(v_decl_835_, sizeof(void*)*3);
v_inlineAttr_x3f_839_ = lean_ctor_get(v_decl_835_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_decl_835_);
if (v_isSharedCheck_864_ == 0)
{
v___x_841_ = v_decl_835_;
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_inlineAttr_x3f_839_);
lean_inc(v_value_837_);
lean_inc(v_toSignature_836_);
lean_dec(v_decl_835_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_name_843_; lean_object* v_type_844_; lean_object* v_params_845_; uint8_t v_safe_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_862_; 
v_name_843_ = lean_ctor_get(v_toSignature_836_, 0);
v_type_844_ = lean_ctor_get(v_toSignature_836_, 2);
v_params_845_ = lean_ctor_get(v_toSignature_836_, 3);
v_safe_846_ = lean_ctor_get_uint8(v_toSignature_836_, sizeof(void*)*4);
v_isSharedCheck_862_ = !lean_is_exclusive(v_toSignature_836_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v_toSignature_836_, 1);
lean_dec(v_unused_863_);
v___x_848_ = v_toSignature_836_;
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_params_845_);
lean_inc(v_type_844_);
lean_inc(v_name_843_);
lean_dec(v_toSignature_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_params_854_; lean_object* v_levelParams_855_; lean_object* v___x_857_; 
v___x_850_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_844_);
v___x_851_ = l_Lean_CollectLevelParams_visitExpr(v_type_844_, v___x_850_);
v___x_852_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_845_, v___x_851_);
lean_inc_ref(v_value_837_);
v___x_853_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_837_, v___x_852_);
v_params_854_ = lean_ctor_get(v___x_853_, 2);
lean_inc_ref(v_params_854_);
lean_dec_ref(v___x_853_);
v_levelParams_855_ = lean_array_to_list(v_params_854_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_levelParams_855_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_name_843_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_levelParams_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_type_844_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_params_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*4, v_safe_846_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_857_);
v___x_859_ = v___x_841_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_value_837_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_inlineAttr_x3f_839_);
lean_ctor_set_uint8(v_reuseFailAlloc_860_, sizeof(void*)*3, v_recursive_838_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Level(builtin);
}
#ifdef __cplusplus
}
#endif
