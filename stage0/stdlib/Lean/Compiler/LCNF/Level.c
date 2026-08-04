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
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_3193__overap_32_; lean_object* v___x_33_; 
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
v___x_3193__overap_32_ = lean_panic_fn_borrowed(v___x_31_, v_msg_8_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v___x_3193__overap_32_, v___y_9_);
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
lean_object* v_a_236_; lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_263_; 
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
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_263_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_snd_243_);
lean_inc(v_fst_242_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v___y_248_; size_t v___x_257_; size_t v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_ptr_addr(v_a_236_);
v___x_258_ = lean_ptr_addr(v_fst_239_);
v___x_259_ = lean_usize_dec_eq(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
v___y_248_ = v___x_259_;
goto v___jp_247_;
}
else
{
size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_ptr_addr(v_a_237_);
v___x_261_ = lean_ptr_addr(v_fst_242_);
v___x_262_ = lean_usize_dec_eq(v___x_260_, v___x_261_);
v___y_248_ = v___x_262_;
goto v___jp_247_;
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_249_ = l_Lean_mkLevelMax_x27(v_fst_239_, v_fst_242_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_snd_243_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_simpLevelMax_x27(v_fst_239_, v_fst_242_, v_u_213_);
lean_dec_ref_known(v_u_213_, 2);
lean_dec(v_fst_242_);
lean_dec(v_fst_239_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_253_);
v___x_255_ = v___x_245_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_snd_243_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
case 3:
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v___x_269_; lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_291_; 
v_a_264_ = lean_ctor_get(v_u_213_, 0);
v_a_265_ = lean_ctor_get(v_u_213_, 1);
lean_inc(v_a_264_);
v___x_266_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_264_, v_a_214_);
v_fst_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_snd_268_);
lean_dec_ref(v___x_266_);
lean_inc(v_a_265_);
v___x_269_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_265_, v_snd_268_);
v_fst_270_ = lean_ctor_get(v___x_269_, 0);
v_snd_271_ = lean_ctor_get(v___x_269_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_291_ == 0)
{
v___x_273_ = v___x_269_;
v_isShared_274_ = v_isSharedCheck_291_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snd_271_);
lean_inc(v_fst_270_);
lean_dec(v___x_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_291_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___y_276_; size_t v___x_285_; size_t v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_ptr_addr(v_a_264_);
v___x_286_ = lean_ptr_addr(v_fst_267_);
v___x_287_ = lean_usize_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_276_ = v___x_287_;
goto v___jp_275_;
}
else
{
size_t v___x_288_; size_t v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_ptr_addr(v_a_265_);
v___x_289_ = lean_ptr_addr(v_fst_270_);
v___x_290_ = lean_usize_dec_eq(v___x_288_, v___x_289_);
v___y_276_ = v___x_290_;
goto v___jp_275_;
}
v___jp_275_:
{
if (v___y_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec_ref_known(v_u_213_, 2);
v___x_277_ = l_Lean_mkLevelIMax_x27(v_fst_267_, v_fst_270_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_277_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_snd_271_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = l_Lean_simpLevelIMax_x27(v_fst_267_, v_fst_270_, v_u_213_);
lean_dec_ref_known(v_u_213_, 2);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_281_);
v___x_283_ = v___x_273_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_snd_271_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
case 4:
{
lean_object* v_a_292_; lean_object* v_nextIdx_293_; lean_object* v_map_294_; lean_object* v_paramNames_295_; lean_object* v___x_296_; 
v_a_292_ = lean_ctor_get(v_u_213_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_u_213_, 1);
v_nextIdx_293_ = lean_ctor_get(v_a_214_, 0);
v_map_294_ = lean_ctor_get(v_a_214_, 1);
v_paramNames_295_ = lean_ctor_get(v_a_214_, 2);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_294_, v_a_292_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_paramNames_295_);
lean_inc_ref(v_map_294_);
lean_inc(v_nextIdx_293_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; 
v_unused_312_ = lean_ctor_get(v_a_214_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_a_214_, 1);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_314_);
v___x_298_ = v_a_214_;
v_isShared_299_ = v_isSharedCheck_311_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_a_214_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_311_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_300_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_293_);
v___x_301_ = lean_name_append_index_after(v___x_300_, v_nextIdx_293_);
v___x_302_ = l_Lean_Level_param___override(v___x_301_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_nextIdx_293_, v___x_303_);
lean_dec(v_nextIdx_293_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_294_, v_a_292_, v___x_302_);
v___x_306_ = lean_array_push(v_paramNames_295_, v_a_292_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_306_);
lean_ctor_set(v___x_298_, 1, v___x_305_);
lean_ctor_set(v___x_298_, 0, v___x_304_);
v___x_308_ = v___x_298_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_306_);
v___x_308_ = v_reuseFailAlloc_310_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_302_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
return v___x_309_;
}
}
}
else
{
lean_object* v_val_315_; lean_object* v___x_316_; 
lean_dec(v_a_292_);
v_val_315_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_296_, 1);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_val_315_);
lean_ctor_set(v___x_316_, 1, v_a_214_);
return v___x_316_;
}
}
default: 
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec_ref_known(v_u_213_, 1);
v___x_317_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_318_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_317_, v_a_214_);
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_320_, v_a_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_323_, v_m_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_m_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_a_329_, lean_object* v_b_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_328_, v_a_329_, v_b_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_332_, lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_336_, v_a_337_, v_x_338_);
lean_dec(v_x_338_);
lean_dec(v_a_337_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
uint8_t v___x_343_; 
v___x_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_344_, lean_object* v_a_345_, lean_object* v_x_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_344_, v_a_345_, v_x_346_);
lean_dec(v_x_346_);
lean_dec(v_a_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_349_, lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_352_, lean_object* v_a_353_, lean_object* v_b_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_353_, v_b_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_357_, lean_object* v_i_358_, lean_object* v_source_359_, lean_object* v_target_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_358_, v_source_359_, v_target_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_363_, v_x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_5181__overap_390_; lean_object* v___x_391_; 
v___f_368_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_369_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_370_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_371_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_372_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___f_368_);
lean_ctor_set(v___x_375_, 1, v___f_369_);
v___x_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___f_370_);
lean_ctor_set(v___x_376_, 2, v___f_371_);
lean_ctor_set(v___x_376_, 3, v___f_372_);
lean_ctor_set(v___x_376_, 4, v___f_373_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___f_374_);
lean_inc_ref_n(v___x_377_, 6);
v___f_378_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_378_, 0, v___x_377_);
v___f_379_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_379_, 0, v___x_377_);
v___f_380_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_380_, 0, v___x_377_);
v___f_381_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_381_, 0, v___x_377_);
v___x_382_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_382_, 0, lean_box(0));
lean_closure_set(v___x_382_, 1, lean_box(0));
lean_closure_set(v___x_382_, 2, v___x_377_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___f_378_);
v___x_384_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, lean_box(0));
lean_closure_set(v___x_384_, 2, v___x_377_);
v___x_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_ctor_set(v___x_385_, 2, v___f_379_);
lean_ctor_set(v___x_385_, 3, v___f_380_);
lean_ctor_set(v___x_385_, 4, v___f_381_);
v___x_386_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_386_, 0, lean_box(0));
lean_closure_set(v___x_386_, 1, lean_box(0));
lean_closure_set(v___x_386_, 2, v___x_377_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_instInhabitedExpr;
v___x_389_ = l_instInhabitedOfMonad___redArg(v___x_387_, v___x_388_);
v___x_5181__overap_390_ = lean_panic_fn_borrowed(v___x_389_, v_msg_366_);
lean_dec(v___x_389_);
v___x_391_ = lean_apply_1(v___x_5181__overap_390_, v___y_367_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v___y_394_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = l_List_reverse___redArg(v_x_393_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___y_394_);
return v___x_396_;
}
else
{
lean_object* v_head_397_; lean_object* v_tail_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_head_397_ = lean_ctor_get(v_x_392_, 0);
v_tail_398_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v_x_392_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_tail_398_);
lean_inc(v_head_397_);
lean_dec(v_x_392_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_406_; 
v___x_402_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_397_, v___y_394_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_snd_404_);
lean_dec_ref(v___x_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_x_393_);
lean_ctor_set(v___x_400_, 0, v_fst_403_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_fst_403_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_x_393_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v_x_392_ = v_tail_398_;
v_x_393_ = v___x_406_;
v___y_394_ = v_snd_404_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_412_ = lean_unsigned_to_nat(26u);
v___x_413_ = lean_unsigned_to_nat(79u);
v___x_414_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_415_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_416_ = l_mkPanicMessageWithDecl(v___x_415_, v___x_414_, v___x_413_, v___x_412_, v___x_411_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_417_, lean_object* v_a_418_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_Expr_hasLevelParam(v_e_417_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_e_417_);
lean_ctor_set(v___x_420_, 1, v_a_418_);
return v___x_420_;
}
else
{
switch(lean_obj_tag(v_e_417_))
{
case 4:
{
lean_object* v_declName_421_; lean_object* v_us_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
v_declName_421_ = lean_ctor_get(v_e_417_, 0);
v_us_422_ = lean_ctor_get(v_e_417_, 1);
v___x_423_ = lean_box(0);
lean_inc(v_us_422_);
v___x_424_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_422_, v___x_423_, v_a_418_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_438_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; 
v___x_430_ = l_ptrEqList___redArg(v_us_422_, v_fst_425_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_declName_421_);
lean_dec_ref_known(v_e_417_, 2);
v___x_431_ = l_Lean_Expr_const___override(v_declName_421_, v_fst_425_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_snd_426_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_object* v___x_436_; 
lean_dec(v_fst_425_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_e_417_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_snd_426_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
case 3:
{
lean_object* v_u_439_; lean_object* v___x_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_456_; 
v_u_439_ = lean_ctor_get(v_e_417_, 0);
lean_inc(v_u_439_);
v___x_440_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_439_, v_a_418_);
v_fst_441_ = lean_ctor_get(v___x_440_, 0);
v_snd_442_ = lean_ctor_get(v___x_440_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_456_ == 0)
{
v___x_444_ = v___x_440_;
v_isShared_445_ = v_isSharedCheck_456_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snd_442_);
lean_inc(v_fst_441_);
lean_dec(v___x_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_456_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
size_t v___x_446_; size_t v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_ptr_addr(v_u_439_);
v___x_447_ = lean_ptr_addr(v_fst_441_);
v___x_448_ = lean_usize_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec_ref_known(v_e_417_, 1);
v___x_449_ = l_Lean_Expr_sort___override(v_fst_441_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_449_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_442_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_fst_441_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_e_417_);
v___x_454_ = v___x_444_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_snd_442_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
case 5:
{
lean_object* v_fn_457_; lean_object* v_arg_458_; lean_object* v___x_459_; lean_object* v_fst_460_; lean_object* v_snd_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_483_; 
v_fn_457_ = lean_ctor_get(v_e_417_, 0);
v_arg_458_ = lean_ctor_get(v_e_417_, 1);
lean_inc_ref(v_fn_457_);
v___x_459_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_457_, v_a_418_);
v_fst_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_fst_460_);
v_snd_461_ = lean_ctor_get(v___x_459_, 1);
lean_inc(v_snd_461_);
lean_dec_ref(v___x_459_);
lean_inc_ref(v_arg_458_);
v___x_462_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_458_, v_snd_461_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
v_snd_464_ = lean_ctor_get(v___x_462_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_483_ == 0)
{
v___x_466_ = v___x_462_;
v_isShared_467_ = v_isSharedCheck_483_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v___x_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_483_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___y_469_; size_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v___x_477_ = lean_ptr_addr(v_fn_457_);
v___x_478_ = lean_ptr_addr(v_fst_460_);
v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
v___y_469_ = v___x_479_;
goto v___jp_468_;
}
else
{
size_t v___x_480_; size_t v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_ptr_addr(v_arg_458_);
v___x_481_ = lean_ptr_addr(v_fst_463_);
v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
v___y_469_ = v___x_482_;
goto v___jp_468_;
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_472_; 
lean_dec_ref_known(v_e_417_, 2);
v___x_470_ = l_Lean_Expr_app___override(v_fst_460_, v_fst_463_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_470_);
v___x_472_ = v___x_466_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_464_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
else
{
lean_object* v___x_475_; 
lean_dec(v_fst_463_);
lean_dec(v_fst_460_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v_e_417_);
v___x_475_ = v___x_466_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_464_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_484_; lean_object* v_type_485_; lean_object* v_value_486_; lean_object* v_body_487_; uint8_t v_nondep_488_; lean_object* v___x_489_; lean_object* v_fst_490_; lean_object* v_snd_491_; lean_object* v___x_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_523_; 
v_declName_484_ = lean_ctor_get(v_e_417_, 0);
v_type_485_ = lean_ctor_get(v_e_417_, 1);
v_value_486_ = lean_ctor_get(v_e_417_, 2);
v_body_487_ = lean_ctor_get(v_e_417_, 3);
v_nondep_488_ = lean_ctor_get_uint8(v_e_417_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_485_);
v___x_489_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_485_, v_a_418_);
v_fst_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_fst_490_);
v_snd_491_ = lean_ctor_get(v___x_489_, 1);
lean_inc(v_snd_491_);
lean_dec_ref(v___x_489_);
lean_inc_ref(v_value_486_);
v___x_492_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_486_, v_snd_491_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v___x_492_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_492_);
lean_inc_ref(v_body_487_);
v___x_495_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_487_, v_snd_494_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_523_ == 0)
{
v___x_499_ = v___x_495_;
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_inc(v_fst_496_);
lean_dec(v___x_495_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___y_502_; size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_type_485_);
v___x_518_ = lean_ptr_addr(v_fst_490_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
v___y_502_ = v___x_519_;
goto v___jp_501_;
}
else
{
size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v_value_486_);
v___x_521_ = lean_ptr_addr(v_fst_493_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
v___y_502_ = v___x_522_;
goto v___jp_501_;
}
v___jp_501_:
{
if (v___y_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_declName_484_);
lean_dec_ref_known(v_e_417_, 4);
v___x_503_ = l_Lean_Expr_letE___override(v_declName_484_, v_fst_490_, v_fst_493_, v_fst_496_, v_nondep_488_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_503_);
v___x_505_ = v___x_499_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_snd_497_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v___x_507_ = lean_ptr_addr(v_body_487_);
v___x_508_ = lean_ptr_addr(v_fst_496_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_inc(v_declName_484_);
lean_dec_ref_known(v_e_417_, 4);
v___x_510_ = l_Lean_Expr_letE___override(v_declName_484_, v_fst_490_, v_fst_493_, v_fst_496_, v_nondep_488_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_510_);
v___x_512_ = v___x_499_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_snd_497_);
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
lean_object* v___x_515_; 
lean_dec(v_fst_496_);
lean_dec(v_fst_493_);
lean_dec(v_fst_490_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_e_417_);
v___x_515_ = v___x_499_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_497_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_524_; lean_object* v_binderType_525_; lean_object* v_body_526_; uint8_t v_binderInfo_527_; lean_object* v___x_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_557_; 
v_binderName_524_ = lean_ctor_get(v_e_417_, 0);
v_binderType_525_ = lean_ctor_get(v_e_417_, 1);
v_body_526_ = lean_ctor_get(v_e_417_, 2);
v_binderInfo_527_ = lean_ctor_get_uint8(v_e_417_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_525_);
v___x_528_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_525_, v_a_418_);
v_fst_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_fst_529_);
v_snd_530_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_snd_530_);
lean_dec_ref(v___x_528_);
lean_inc_ref(v_body_526_);
v___x_531_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_526_, v_snd_530_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_557_ == 0)
{
v___x_535_ = v___x_531_;
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snd_533_);
lean_inc(v_fst_532_);
lean_dec(v___x_531_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_557_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint8_t v___y_538_; size_t v___x_551_; size_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_ptr_addr(v_binderType_525_);
v___x_552_ = lean_ptr_addr(v_fst_529_);
v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
v___y_538_ = v___x_553_;
goto v___jp_537_;
}
else
{
size_t v___x_554_; size_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_ptr_addr(v_body_526_);
v___x_555_ = lean_ptr_addr(v_fst_532_);
v___x_556_ = lean_usize_dec_eq(v___x_554_, v___x_555_);
v___y_538_ = v___x_556_;
goto v___jp_537_;
}
v___jp_537_:
{
if (v___y_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_541_; 
lean_inc(v_binderName_524_);
lean_dec_ref_known(v_e_417_, 3);
v___x_539_ = l_Lean_Expr_forallE___override(v_binderName_524_, v_fst_529_, v_fst_532_, v_binderInfo_527_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_snd_533_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
else
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_527_, v_binderInfo_527_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_546_; 
lean_inc(v_binderName_524_);
lean_dec_ref_known(v_e_417_, 3);
v___x_544_ = l_Lean_Expr_forallE___override(v_binderName_524_, v_fst_529_, v_fst_532_, v_binderInfo_527_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_544_);
v___x_546_ = v___x_535_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_snd_533_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v_fst_532_);
lean_dec(v_fst_529_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_e_417_);
v___x_549_ = v___x_535_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_533_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_558_; lean_object* v_binderType_559_; lean_object* v_body_560_; uint8_t v_binderInfo_561_; lean_object* v___x_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_591_; 
v_binderName_558_ = lean_ctor_get(v_e_417_, 0);
v_binderType_559_ = lean_ctor_get(v_e_417_, 1);
v_body_560_ = lean_ctor_get(v_e_417_, 2);
v_binderInfo_561_ = lean_ctor_get_uint8(v_e_417_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_559_);
v___x_562_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_559_, v_a_418_);
v_fst_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v___x_562_);
lean_inc_ref(v_body_560_);
v___x_565_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_560_, v_snd_564_);
v_fst_566_ = lean_ctor_get(v___x_565_, 0);
v_snd_567_ = lean_ctor_get(v___x_565_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_591_ == 0)
{
v___x_569_ = v___x_565_;
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
lean_dec(v___x_565_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___y_572_; size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_ptr_addr(v_binderType_559_);
v___x_586_ = lean_ptr_addr(v_fst_563_);
v___x_587_ = lean_usize_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
v___y_572_ = v___x_587_;
goto v___jp_571_;
}
else
{
size_t v___x_588_; size_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_ptr_addr(v_body_560_);
v___x_589_ = lean_ptr_addr(v_fst_566_);
v___x_590_ = lean_usize_dec_eq(v___x_588_, v___x_589_);
v___y_572_ = v___x_590_;
goto v___jp_571_;
}
v___jp_571_:
{
if (v___y_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc(v_binderName_558_);
lean_dec_ref_known(v_e_417_, 3);
v___x_573_ = l_Lean_Expr_lam___override(v_binderName_558_, v_fst_563_, v_fst_566_, v_binderInfo_561_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_573_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_snd_567_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
uint8_t v___x_577_; 
v___x_577_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_561_, v_binderInfo_561_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_inc(v_binderName_558_);
lean_dec_ref_known(v_e_417_, 3);
v___x_578_ = l_Lean_Expr_lam___override(v_binderName_558_, v_fst_563_, v_fst_566_, v_binderInfo_561_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_578_);
v___x_580_ = v___x_569_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_567_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v___x_583_; 
lean_dec(v_fst_566_);
lean_dec(v_fst_563_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_e_417_);
v___x_583_ = v___x_569_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_snd_567_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_592_; lean_object* v_expr_593_; lean_object* v___x_594_; lean_object* v_fst_595_; lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_610_; 
v_data_592_ = lean_ctor_get(v_e_417_, 0);
v_expr_593_ = lean_ctor_get(v_e_417_, 1);
lean_inc_ref(v_expr_593_);
v___x_594_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_593_, v_a_418_);
v_fst_595_ = lean_ctor_get(v___x_594_, 0);
v_snd_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_610_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_inc(v_fst_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
size_t v___x_600_; size_t v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_ptr_addr(v_expr_593_);
v___x_601_ = lean_ptr_addr(v_fst_595_);
v___x_602_ = lean_usize_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_inc(v_data_592_);
lean_dec_ref_known(v_e_417_, 2);
v___x_603_ = l_Lean_Expr_mdata___override(v_data_592_, v_fst_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_603_);
v___x_605_ = v___x_598_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_snd_596_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
lean_object* v___x_608_; 
lean_dec(v_fst_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_e_417_);
v___x_608_ = v___x_598_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_snd_596_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
case 11:
{
lean_object* v_typeName_611_; lean_object* v_idx_612_; lean_object* v_struct_613_; lean_object* v___x_614_; lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_630_; 
v_typeName_611_ = lean_ctor_get(v_e_417_, 0);
v_idx_612_ = lean_ctor_get(v_e_417_, 1);
v_struct_613_ = lean_ctor_get(v_e_417_, 2);
lean_inc_ref(v_struct_613_);
v___x_614_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_613_, v_a_418_);
v_fst_615_ = lean_ctor_get(v___x_614_, 0);
v_snd_616_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_630_ == 0)
{
v___x_618_ = v___x_614_;
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_inc(v_fst_615_);
lean_dec(v___x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_630_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
size_t v___x_620_; size_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_ptr_addr(v_struct_613_);
v___x_621_ = lean_ptr_addr(v_fst_615_);
v___x_622_ = lean_usize_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_625_; 
lean_inc(v_idx_612_);
lean_inc(v_typeName_611_);
lean_dec_ref_known(v_e_417_, 3);
v___x_623_ = l_Lean_Expr_proj___override(v_typeName_611_, v_idx_612_, v_fst_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_623_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_snd_616_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v___x_628_; 
lean_dec(v_fst_615_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_e_417_);
v___x_628_ = v___x_618_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_e_417_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_616_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
case 2:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec_ref_known(v_e_417_, 1);
v___x_631_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_632_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_631_, v_a_418_);
return v___x_632_;
}
default: 
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_e_417_);
lean_ctor_set(v___x_633_, 1, v_a_418_);
return v___x_633_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_box(0);
v___x_635_ = lean_unsigned_to_nat(16u);
v___x_636_ = lean_mk_array(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_643_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_snd_649_; lean_object* v_fst_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
v___x_647_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_648_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_646_, v___x_647_);
v_snd_649_ = lean_ctor_get(v___x_648_, 1);
v_fst_650_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_659_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snd_649_);
lean_inc(v_fst_650_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_paramNames_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v_paramNames_654_ = lean_ctor_get(v_snd_649_, 2);
lean_inc_ref(v_paramNames_654_);
lean_dec(v_snd_649_);
v___x_655_ = lean_array_to_list(v_paramNames_654_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_CollectLevelParams_visitExpr(v_type_660_, v_a_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_663_, lean_object* v_a_664_){
_start:
{
if (lean_obj_tag(v_arg_663_) == 2)
{
lean_object* v_expr_665_; lean_object* v___x_666_; 
v_expr_665_ = lean_ctor_get(v_arg_663_, 0);
lean_inc_ref(v_expr_665_);
lean_dec_ref_known(v_arg_663_, 1);
v___x_666_ = l_Lean_CollectLevelParams_visitExpr(v_expr_665_, v_a_664_);
return v___x_666_;
}
else
{
lean_dec(v_arg_663_);
return v_a_664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_667_, size_t v_i_668_, size_t v_stop_669_, lean_object* v_b_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_eq(v_i_668_, v_stop_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; size_t v___x_674_; size_t v___x_675_; 
v___x_672_ = lean_array_uget_borrowed(v_as_667_, v_i_668_);
lean_inc(v___x_672_);
v___x_673_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_672_, v_b_670_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_668_, v___x_674_);
v_i_668_ = v___x_675_;
v_b_670_ = v___x_673_;
goto _start;
}
else
{
return v_b_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_, lean_object* v_b_680_){
_start:
{
size_t v_i_boxed_681_; size_t v_stop_boxed_682_; lean_object* v_res_683_; 
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_682_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_677_, v_i_boxed_681_, v_stop_boxed_682_, v_b_680_);
lean_dec_ref(v_as_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_684_, lean_object* v_s_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_args_684_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
return v_s_685_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = lean_nat_dec_le(v___x_687_, v___x_687_);
if (v___x_689_ == 0)
{
if (v___x_688_ == 0)
{
return v_s_685_;
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_687_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_684_, v___x_690_, v___x_691_, v_s_685_);
return v___x_692_;
}
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_687_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_684_, v___x_693_, v___x_694_, v_s_685_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_696_, lean_object* v_s_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_696_, v_s_697_);
lean_dec_ref(v_args_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_699_, lean_object* v_a_700_){
_start:
{
switch(lean_obj_tag(v_e_699_))
{
case 3:
{
lean_object* v_us_701_; lean_object* v_args_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_us_701_ = lean_ctor_get(v_e_699_, 1);
lean_inc(v_us_701_);
v_args_702_ = lean_ctor_get(v_e_699_, 2);
lean_inc_ref(v_args_702_);
lean_dec_ref_known(v_e_699_, 3);
v___x_703_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_702_, v_a_700_);
lean_dec_ref(v_args_702_);
v___x_704_ = l_Lean_CollectLevelParams_visitLevels(v_us_701_, v___x_703_);
return v___x_704_;
}
case 4:
{
lean_object* v_args_705_; lean_object* v___x_706_; 
v_args_705_ = lean_ctor_get(v_e_699_, 1);
lean_inc_ref(v_args_705_);
lean_dec_ref_known(v_e_699_, 2);
v___x_706_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_705_, v_a_700_);
lean_dec_ref(v_args_705_);
return v___x_706_;
}
default: 
{
lean_dec(v_e_699_);
return v_a_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_type_709_; lean_object* v___x_710_; 
v_type_709_ = lean_ctor_get(v_p_707_, 2);
lean_inc_ref(v_type_709_);
lean_dec_ref(v_p_707_);
v___x_710_ = l_Lean_CollectLevelParams_visitExpr(v_type_709_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_711_, size_t v_i_712_, size_t v_stop_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_eq(v_i_712_, v_stop_713_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; size_t v___x_718_; size_t v___x_719_; 
v___x_716_ = lean_array_uget_borrowed(v_as_711_, v_i_712_);
lean_inc(v___x_716_);
v___x_717_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_716_, v_b_714_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_712_, v___x_718_);
v_i_712_ = v___x_719_;
v_b_714_ = v___x_717_;
goto _start;
}
else
{
return v_b_714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_721_, lean_object* v_i_722_, lean_object* v_stop_723_, lean_object* v_b_724_){
_start:
{
size_t v_i_boxed_725_; size_t v_stop_boxed_726_; lean_object* v_res_727_; 
v_i_boxed_725_ = lean_unbox_usize(v_i_722_);
lean_dec(v_i_722_);
v_stop_boxed_726_ = lean_unbox_usize(v_stop_723_);
lean_dec(v_stop_723_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_721_, v_i_boxed_725_, v_stop_boxed_726_, v_b_724_);
lean_dec_ref(v_as_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_728_, lean_object* v_s_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_array_get_size(v_ps_728_);
v___x_732_ = lean_nat_dec_lt(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
return v_s_729_;
}
else
{
uint8_t v___x_733_; 
v___x_733_ = lean_nat_dec_le(v___x_731_, v___x_731_);
if (v___x_733_ == 0)
{
if (v___x_732_ == 0)
{
return v_s_729_;
}
else
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((size_t)0ULL);
v___x_735_ = lean_usize_of_nat(v___x_731_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_728_, v___x_734_, v___x_735_, v_s_729_);
return v___x_736_;
}
}
else
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_731_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_728_, v___x_737_, v___x_738_, v_s_729_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_740_, lean_object* v_s_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_740_, v_s_741_);
lean_dec_ref(v_ps_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_743_, size_t v_i_744_, size_t v_stop_745_, lean_object* v_b_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_744_, v_stop_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; size_t v___x_750_; size_t v___x_751_; 
v___x_748_ = lean_array_uget_borrowed(v_as_743_, v_i_744_);
lean_inc(v___x_748_);
v___x_749_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_748_, v_b_746_);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_744_, v___x_750_);
v_i_744_ = v___x_751_;
v_b_746_ = v___x_749_;
goto _start;
}
else
{
return v_b_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_753_, lean_object* v_s_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_alts_753_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
return v_s_754_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_758_ == 0)
{
if (v___x_757_ == 0)
{
return v_s_754_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_756_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_753_, v___x_759_, v___x_760_, v_s_754_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_756_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_753_, v___x_762_, v___x_763_, v_s_754_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_765_, lean_object* v_a_766_){
_start:
{
switch(lean_obj_tag(v_x_765_))
{
case 0:
{
lean_object* v_decl_767_; lean_object* v_k_768_; lean_object* v_type_769_; lean_object* v_value_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_decl_767_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_decl_767_);
v_k_768_ = lean_ctor_get(v_x_765_, 1);
lean_inc_ref(v_k_768_);
lean_dec_ref_known(v_x_765_, 2);
v_type_769_ = lean_ctor_get(v_decl_767_, 2);
lean_inc_ref(v_type_769_);
v_value_770_ = lean_ctor_get(v_decl_767_, 3);
lean_inc(v_value_770_);
lean_dec_ref(v_decl_767_);
v___x_771_ = l_Lean_CollectLevelParams_visitExpr(v_type_769_, v_a_766_);
v___x_772_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_770_, v___x_771_);
v_x_765_ = v_k_768_;
v_a_766_ = v___x_772_;
goto _start;
}
case 3:
{
lean_object* v_args_774_; lean_object* v___x_775_; 
v_args_774_ = lean_ctor_get(v_x_765_, 1);
lean_inc_ref(v_args_774_);
lean_dec_ref_known(v_x_765_, 2);
v___x_775_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_774_, v_a_766_);
lean_dec_ref(v_args_774_);
return v___x_775_;
}
case 4:
{
lean_object* v_cases_776_; lean_object* v_resultType_777_; lean_object* v_alts_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_cases_776_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_cases_776_);
lean_dec_ref_known(v_x_765_, 1);
v_resultType_777_ = lean_ctor_get(v_cases_776_, 1);
lean_inc_ref(v_resultType_777_);
v_alts_778_ = lean_ctor_get(v_cases_776_, 3);
lean_inc_ref(v_alts_778_);
lean_dec_ref(v_cases_776_);
v___x_779_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_777_, v_a_766_);
v___x_780_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_778_, v___x_779_);
lean_dec_ref(v_alts_778_);
return v___x_780_;
}
case 5:
{
lean_dec_ref_known(v_x_765_, 1);
return v_a_766_;
}
case 6:
{
lean_object* v_type_781_; lean_object* v___x_782_; 
v_type_781_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_type_781_);
lean_dec_ref_known(v_x_765_, 1);
v___x_782_ = l_Lean_CollectLevelParams_visitExpr(v_type_781_, v_a_766_);
return v___x_782_;
}
default: 
{
lean_object* v_decl_783_; lean_object* v_k_784_; lean_object* v_params_785_; lean_object* v_type_786_; lean_object* v_value_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_decl_783_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_decl_783_);
v_k_784_ = lean_ctor_get(v_x_765_, 1);
lean_inc_ref(v_k_784_);
lean_dec_ref(v_x_765_);
v_params_785_ = lean_ctor_get(v_decl_783_, 2);
lean_inc_ref(v_params_785_);
v_type_786_ = lean_ctor_get(v_decl_783_, 3);
lean_inc_ref(v_type_786_);
v_value_787_ = lean_ctor_get(v_decl_783_, 4);
lean_inc_ref(v_value_787_);
lean_dec_ref(v_decl_783_);
v___x_788_ = l_Lean_CollectLevelParams_visitExpr(v_type_786_, v_a_766_);
v___x_789_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_785_, v___x_788_);
lean_dec_ref(v_params_785_);
v___x_790_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_787_, v___x_789_);
v_x_765_ = v_k_784_;
v_a_766_ = v___x_790_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_792_, lean_object* v_a_793_){
_start:
{
if (lean_obj_tag(v_alt_792_) == 0)
{
lean_object* v_params_794_; lean_object* v_code_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_params_794_ = lean_ctor_get(v_alt_792_, 1);
lean_inc_ref(v_params_794_);
v_code_795_ = lean_ctor_get(v_alt_792_, 2);
lean_inc_ref(v_code_795_);
lean_dec_ref_known(v_alt_792_, 3);
v___x_796_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_794_, v_a_793_);
lean_dec_ref(v_params_794_);
v___x_797_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_795_, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v_code_798_; lean_object* v___x_799_; 
v_code_798_ = lean_ctor_get(v_alt_792_, 0);
lean_inc_ref(v_code_798_);
lean_dec_ref_known(v_alt_792_, 1);
v___x_799_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_798_, v_a_793_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_800_, lean_object* v_i_801_, lean_object* v_stop_802_, lean_object* v_b_803_){
_start:
{
size_t v_i_boxed_804_; size_t v_stop_boxed_805_; lean_object* v_res_806_; 
v_i_boxed_804_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_stop_boxed_805_ = lean_unbox_usize(v_stop_802_);
lean_dec(v_stop_802_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_800_, v_i_boxed_804_, v_stop_boxed_805_, v_b_803_);
lean_dec_ref(v_as_800_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_807_, lean_object* v_s_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_807_, v_s_808_);
lean_dec_ref(v_alts_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_810_, lean_object* v_a_811_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v_code_812_; lean_object* v___x_813_; 
v_code_812_ = lean_ctor_get(v_x_810_, 0);
lean_inc_ref(v_code_812_);
lean_dec_ref_known(v_x_810_, 1);
v___x_813_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_812_, v_a_811_);
return v___x_813_;
}
else
{
lean_dec_ref_known(v_x_810_, 1);
return v_a_811_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_unsigned_to_nat(16u);
v___x_816_ = lean_mk_array(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_821_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
lean_ctor_set(v___x_822_, 2, v___x_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_823_){
_start:
{
lean_object* v_toSignature_824_; lean_object* v_value_825_; uint8_t v_recursive_826_; lean_object* v_inlineAttr_x3f_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_852_; 
v_toSignature_824_ = lean_ctor_get(v_decl_823_, 0);
v_value_825_ = lean_ctor_get(v_decl_823_, 1);
v_recursive_826_ = lean_ctor_get_uint8(v_decl_823_, sizeof(void*)*3);
v_inlineAttr_x3f_827_ = lean_ctor_get(v_decl_823_, 2);
v_isSharedCheck_852_ = !lean_is_exclusive(v_decl_823_);
if (v_isSharedCheck_852_ == 0)
{
v___x_829_ = v_decl_823_;
v_isShared_830_ = v_isSharedCheck_852_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_inlineAttr_x3f_827_);
lean_inc(v_value_825_);
lean_inc(v_toSignature_824_);
lean_dec(v_decl_823_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_852_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_name_831_; lean_object* v_type_832_; lean_object* v_params_833_; uint8_t v_safe_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_850_; 
v_name_831_ = lean_ctor_get(v_toSignature_824_, 0);
v_type_832_ = lean_ctor_get(v_toSignature_824_, 2);
v_params_833_ = lean_ctor_get(v_toSignature_824_, 3);
v_safe_834_ = lean_ctor_get_uint8(v_toSignature_824_, sizeof(void*)*4);
v_isSharedCheck_850_ = !lean_is_exclusive(v_toSignature_824_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_toSignature_824_, 1);
lean_dec(v_unused_851_);
v___x_836_ = v_toSignature_824_;
v_isShared_837_ = v_isSharedCheck_850_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_params_833_);
lean_inc(v_type_832_);
lean_inc(v_name_831_);
lean_dec(v_toSignature_824_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_850_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_params_842_; lean_object* v_levelParams_843_; lean_object* v___x_845_; 
v___x_838_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_832_);
v___x_839_ = l_Lean_CollectLevelParams_visitExpr(v_type_832_, v___x_838_);
v___x_840_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_833_, v___x_839_);
lean_inc_ref(v_value_825_);
v___x_841_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_825_, v___x_840_);
v_params_842_ = lean_ctor_get(v___x_841_, 2);
lean_inc_ref(v_params_842_);
lean_dec_ref(v___x_841_);
v_levelParams_843_ = lean_array_to_list(v_params_842_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_levelParams_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_name_831_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_levelParams_843_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_type_832_);
lean_ctor_set(v_reuseFailAlloc_849_, 3, v_params_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_849_, sizeof(void*)*4, v_safe_834_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_845_);
v___x_847_ = v___x_829_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_value_825_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_inlineAttr_x3f_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_848_, sizeof(void*)*3, v_recursive_826_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
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
