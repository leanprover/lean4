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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0;
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
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_3042__overap_32_; lean_object* v___x_33_; 
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
v___x_3042__overap_32_ = lean_panic_fn_borrowed(v___x_31_, v_msg_8_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v___x_3042__overap_32_, v___y_9_);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; uint64_t v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1723u);
v___x_53_ = lean_uint64_of_nat(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
return v_x_54_;
}
else
{
lean_object* v_key_56_; lean_object* v_value_57_; lean_object* v_tail_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_84_; 
v_key_56_ = lean_ctor_get(v_x_55_, 0);
v_value_57_ = lean_ctor_get(v_x_55_, 1);
v_tail_58_ = lean_ctor_get(v_x_55_, 2);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_84_ == 0)
{
v___x_60_ = v_x_55_;
v_isShared_61_ = v_isSharedCheck_84_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_tail_58_);
lean_inc(v_value_57_);
lean_inc(v_key_56_);
lean_dec(v_x_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_84_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; uint64_t v___y_64_; 
v___x_62_ = lean_array_get_size(v_x_54_);
if (lean_obj_tag(v_key_56_) == 0)
{
uint64_t v___x_82_; 
v___x_82_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___y_64_ = v___x_82_;
goto v___jp_63_;
}
else
{
uint64_t v_hash_83_; 
v_hash_83_ = lean_ctor_get_uint64(v_key_56_, sizeof(void*)*2);
v___y_64_ = v_hash_83_;
goto v___jp_63_;
}
v___jp_63_:
{
uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v_fold_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_65_ = 32ULL;
v___x_66_ = lean_uint64_shift_right(v___y_64_, v___x_65_);
v_fold_67_ = lean_uint64_xor(v___y_64_, v___x_66_);
v___x_68_ = 16ULL;
v___x_69_ = lean_uint64_shift_right(v_fold_67_, v___x_68_);
v___x_70_ = lean_uint64_xor(v_fold_67_, v___x_69_);
v___x_71_ = lean_uint64_to_usize(v___x_70_);
v___x_72_ = lean_usize_of_nat(v___x_62_);
v___x_73_ = ((size_t)1ULL);
v___x_74_ = lean_usize_sub(v___x_72_, v___x_73_);
v___x_75_ = lean_usize_land(v___x_71_, v___x_74_);
v___x_76_ = lean_array_uget_borrowed(v_x_54_, v___x_75_);
lean_inc(v___x_76_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 2, v___x_76_);
v___x_78_ = v___x_60_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_key_56_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_value_57_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v___x_76_);
v___x_78_ = v_reuseFailAlloc_81_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_79_; 
v___x_79_ = lean_array_uset(v_x_54_, v___x_75_, v___x_78_);
v_x_54_ = v___x_79_;
v_x_55_ = v_tail_58_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(lean_object* v_i_85_, lean_object* v_source_86_, lean_object* v_target_87_){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_array_get_size(v_source_86_);
v___x_89_ = lean_nat_dec_lt(v_i_85_, v___x_88_);
if (v___x_89_ == 0)
{
lean_dec_ref(v_source_86_);
lean_dec(v_i_85_);
return v_target_87_;
}
else
{
lean_object* v_es_90_; lean_object* v___x_91_; lean_object* v_source_92_; lean_object* v_target_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_es_90_ = lean_array_fget(v_source_86_, v_i_85_);
v___x_91_ = lean_box(0);
v_source_92_ = lean_array_fset(v_source_86_, v_i_85_, v___x_91_);
v_target_93_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_target_87_, v_es_90_);
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = lean_nat_add(v_i_85_, v___x_94_);
lean_dec(v_i_85_);
v_i_85_ = v___x_95_;
v_source_86_ = v_source_92_;
v_target_87_ = v_target_93_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(lean_object* v_data_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_nbuckets_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_98_ = lean_array_get_size(v_data_97_);
v___x_99_ = lean_unsigned_to_nat(2u);
v_nbuckets_100_ = lean_nat_mul(v___x_98_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_box(0);
v___x_103_ = lean_mk_array(v_nbuckets_100_, v___x_102_);
v___x_104_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v___x_101_, v_data_97_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object* v_a_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
else
{
lean_object* v_key_108_; lean_object* v_tail_109_; uint8_t v___x_110_; 
v_key_108_ = lean_ctor_get(v_x_106_, 0);
v_tail_109_ = lean_ctor_get(v_x_106_, 2);
v___x_110_ = lean_name_eq(v_key_108_, v_a_105_);
if (v___x_110_ == 0)
{
v_x_106_ = v_tail_109_;
goto _start;
}
else
{
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object* v_a_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_112_, v_x_113_);
lean_dec(v_x_113_);
lean_dec(v_a_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object* v_m_116_, lean_object* v_a_117_, lean_object* v_b_118_){
_start:
{
lean_object* v_size_119_; lean_object* v_buckets_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_166_; 
v_size_119_ = lean_ctor_get(v_m_116_, 0);
v_buckets_120_ = lean_ctor_get(v_m_116_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_m_116_);
if (v_isSharedCheck_166_ == 0)
{
v___x_122_ = v_m_116_;
v_isShared_123_ = v_isSharedCheck_166_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_buckets_120_);
lean_inc(v_size_119_);
lean_dec(v_m_116_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_166_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; uint64_t v___y_126_; 
v___x_124_ = lean_array_get_size(v_buckets_120_);
if (lean_obj_tag(v_a_117_) == 0)
{
uint64_t v___x_164_; 
v___x_164_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___y_126_ = v___x_164_;
goto v___jp_125_;
}
else
{
uint64_t v_hash_165_; 
v_hash_165_ = lean_ctor_get_uint64(v_a_117_, sizeof(void*)*2);
v___y_126_ = v_hash_165_;
goto v___jp_125_;
}
v___jp_125_:
{
uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v_bkt_138_; uint8_t v___x_139_; 
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___y_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___y_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_124_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v_bkt_138_ = lean_array_uget_borrowed(v_buckets_120_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_117_, v_bkt_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v_size_x27_141_; lean_object* v___x_142_; lean_object* v_buckets_x27_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v_size_x27_141_ = lean_nat_add(v_size_119_, v___x_140_);
lean_dec(v_size_119_);
lean_inc(v_bkt_138_);
v___x_142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_142_, 0, v_a_117_);
lean_ctor_set(v___x_142_, 1, v_b_118_);
lean_ctor_set(v___x_142_, 2, v_bkt_138_);
v_buckets_x27_143_ = lean_array_uset(v_buckets_120_, v___x_137_, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_mul(v_size_x27_141_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(3u);
v___x_147_ = lean_nat_div(v___x_145_, v___x_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_array_get_size(v_buckets_x27_143_);
v___x_149_ = lean_nat_dec_le(v___x_147_, v___x_148_);
lean_dec(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v_val_150_; lean_object* v___x_152_; 
v_val_150_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_buckets_x27_143_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_val_150_);
lean_ctor_set(v___x_122_, 0, v_size_x27_141_);
v___x_152_ = v___x_122_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_size_x27_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_val_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v___x_155_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_buckets_x27_143_);
lean_ctor_set(v___x_122_, 0, v_size_x27_141_);
v___x_155_ = v___x_122_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_size_x27_141_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_buckets_x27_143_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_inc(v_bkt_138_);
v___x_157_ = lean_box(0);
v_buckets_x27_158_ = lean_array_uset(v_buckets_120_, v___x_137_, v___x_157_);
v___x_159_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_117_, v_b_118_, v_bkt_138_);
v___x_160_ = lean_array_uset(v_buckets_x27_158_, v___x_137_, v___x_159_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_160_);
v___x_162_ = v___x_122_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_119_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object* v_a_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v_key_170_; lean_object* v_value_171_; lean_object* v_tail_172_; uint8_t v___x_173_; 
v_key_170_ = lean_ctor_get(v_x_168_, 0);
v_value_171_ = lean_ctor_get(v_x_168_, 1);
v_tail_172_ = lean_ctor_get(v_x_168_, 2);
v___x_173_ = lean_name_eq(v_key_170_, v_a_167_);
if (v___x_173_ == 0)
{
v_x_168_ = v_tail_172_;
goto _start;
}
else
{
lean_object* v___x_175_; 
lean_inc(v_value_171_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_value_171_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_176_, v_x_177_);
lean_dec(v_x_177_);
lean_dec(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_buckets_181_; lean_object* v___x_182_; uint64_t v___y_184_; 
v_buckets_181_ = lean_ctor_get(v_m_179_, 1);
v___x_182_ = lean_array_get_size(v_buckets_181_);
if (lean_obj_tag(v_a_180_) == 0)
{
uint64_t v___x_198_; 
v___x_198_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___y_184_ = v___x_198_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_199_; 
v_hash_199_ = lean_ctor_get_uint64(v_a_180_, sizeof(void*)*2);
v___y_184_ = v_hash_199_;
goto v___jp_183_;
}
v___jp_183_:
{
uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_fold_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_185_ = 32ULL;
v___x_186_ = lean_uint64_shift_right(v___y_184_, v___x_185_);
v_fold_187_ = lean_uint64_xor(v___y_184_, v___x_186_);
v___x_188_ = 16ULL;
v___x_189_ = lean_uint64_shift_right(v_fold_187_, v___x_188_);
v___x_190_ = lean_uint64_xor(v_fold_187_, v___x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = lean_usize_of_nat(v___x_182_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_sub(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_land(v___x_191_, v___x_194_);
v___x_196_ = lean_array_uget_borrowed(v_buckets_181_, v___x_195_);
v___x_197_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_180_, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg___boxed(lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_m_200_);
return v_res_202_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_209_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_210_ = lean_unsigned_to_nat(19u);
v___x_211_ = lean_unsigned_to_nat(55u);
v___x_212_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3));
v___x_213_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_214_ = l_mkPanicMessageWithDecl(v___x_213_, v___x_212_, v___x_211_, v___x_210_, v___x_209_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel(lean_object* v_u_215_, lean_object* v_a_216_){
_start:
{
uint8_t v___x_217_; uint8_t v___x_218_; 
v___x_217_ = l_Lean_Level_hasParam(v_u_215_);
v___x_218_ = lean_bool_not(v___x_217_);
if (v___x_218_ == 0)
{
switch(lean_obj_tag(v_u_215_))
{
case 0:
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_u_215_);
lean_ctor_set(v___x_219_, 1, v_a_216_);
return v___x_219_;
}
case 1:
{
lean_object* v_a_220_; lean_object* v___x_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_237_; 
v_a_220_ = lean_ctor_get(v_u_215_, 0);
lean_inc(v_a_220_);
v___x_221_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_220_, v_a_216_);
v_fst_222_ = lean_ctor_get(v___x_221_, 0);
v_snd_223_ = lean_ctor_get(v___x_221_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_237_ == 0)
{
v___x_225_ = v___x_221_;
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snd_223_);
lean_inc(v_fst_222_);
lean_dec(v___x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_237_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
size_t v___x_227_; size_t v___x_228_; uint8_t v___x_229_; 
v___x_227_ = lean_ptr_addr(v_a_220_);
v___x_228_ = lean_ptr_addr(v_fst_222_);
v___x_229_ = lean_usize_dec_eq(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec_ref_known(v_u_215_, 1);
v___x_230_ = l_Lean_Level_succ___override(v_fst_222_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_230_);
v___x_232_ = v___x_225_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_snd_223_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v___x_235_; 
lean_dec(v_fst_222_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v_u_215_);
v___x_235_ = v___x_225_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_u_215_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_snd_223_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
case 2:
{
lean_object* v_a_238_; lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_243_; lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_265_; 
v_a_238_ = lean_ctor_get(v_u_215_, 0);
v_a_239_ = lean_ctor_get(v_u_215_, 1);
lean_inc(v_a_238_);
v___x_240_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_238_, v_a_216_);
v_fst_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_fst_241_);
v_snd_242_ = lean_ctor_get(v___x_240_, 1);
lean_inc(v_snd_242_);
lean_dec_ref(v___x_240_);
lean_inc(v_a_239_);
v___x_243_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_239_, v_snd_242_);
v_fst_244_ = lean_ctor_get(v___x_243_, 0);
v_snd_245_ = lean_ctor_get(v___x_243_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_265_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snd_245_);
lean_inc(v_fst_244_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___y_250_; size_t v___x_259_; size_t v___x_260_; uint8_t v___x_261_; 
v___x_259_ = lean_ptr_addr(v_a_238_);
v___x_260_ = lean_ptr_addr(v_fst_241_);
v___x_261_ = lean_usize_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
v___y_250_ = v___x_261_;
goto v___jp_249_;
}
else
{
size_t v___x_262_; size_t v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_ptr_addr(v_a_239_);
v___x_263_ = lean_ptr_addr(v_fst_244_);
v___x_264_ = lean_usize_dec_eq(v___x_262_, v___x_263_);
v___y_250_ = v___x_264_;
goto v___jp_249_;
}
v___jp_249_:
{
if (v___y_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_251_ = l_Lean_mkLevelMax_x27(v_fst_241_, v_fst_244_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_251_);
v___x_253_ = v___x_247_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_245_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = l_Lean_simpLevelMax_x27(v_fst_241_, v_fst_244_, v_u_215_);
lean_dec_ref_known(v_u_215_, 2);
lean_dec(v_fst_244_);
lean_dec(v_fst_241_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_255_);
v___x_257_ = v___x_247_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_snd_245_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
case 3:
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_293_; 
v_a_266_ = lean_ctor_get(v_u_215_, 0);
v_a_267_ = lean_ctor_get(v_u_215_, 1);
lean_inc(v_a_266_);
v___x_268_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_266_, v_a_216_);
v_fst_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_fst_269_);
v_snd_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v___x_268_);
lean_inc(v_a_267_);
v___x_271_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_267_, v_snd_270_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
v_snd_273_ = lean_ctor_get(v___x_271_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_293_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_snd_273_);
lean_inc(v_fst_272_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___y_278_; size_t v___x_287_; size_t v___x_288_; uint8_t v___x_289_; 
v___x_287_ = lean_ptr_addr(v_a_266_);
v___x_288_ = lean_ptr_addr(v_fst_269_);
v___x_289_ = lean_usize_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
v___y_278_ = v___x_289_;
goto v___jp_277_;
}
else
{
size_t v___x_290_; size_t v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_ptr_addr(v_a_267_);
v___x_291_ = lean_ptr_addr(v_fst_272_);
v___x_292_ = lean_usize_dec_eq(v___x_290_, v___x_291_);
v___y_278_ = v___x_292_;
goto v___jp_277_;
}
v___jp_277_:
{
if (v___y_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_279_ = l_Lean_mkLevelIMax_x27(v_fst_269_, v_fst_272_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_279_);
v___x_281_ = v___x_275_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_snd_273_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = l_Lean_simpLevelIMax_x27(v_fst_269_, v_fst_272_, v_u_215_);
lean_dec_ref_known(v_u_215_, 2);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_283_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_273_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
case 4:
{
lean_object* v_a_294_; lean_object* v_nextIdx_295_; lean_object* v_map_296_; lean_object* v_paramNames_297_; lean_object* v___x_298_; 
v_a_294_ = lean_ctor_get(v_u_215_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v_u_215_, 1);
v_nextIdx_295_ = lean_ctor_get(v_a_216_, 0);
v_map_296_ = lean_ctor_get(v_a_216_, 1);
v_paramNames_297_ = lean_ctor_get(v_a_216_, 2);
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_296_, v_a_294_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_313_; 
lean_inc_ref(v_paramNames_297_);
lean_inc_ref(v_map_296_);
lean_inc(v_nextIdx_295_);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_314_ = lean_ctor_get(v_a_216_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_a_216_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_a_216_, 0);
lean_dec(v_unused_316_);
v___x_300_ = v_a_216_;
v_isShared_301_ = v_isSharedCheck_313_;
goto v_resetjp_299_;
}
else
{
lean_dec(v_a_216_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_313_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_302_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_295_);
v___x_303_ = lean_name_append_index_after(v___x_302_, v_nextIdx_295_);
v___x_304_ = l_Lean_Level_param___override(v___x_303_);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_add(v_nextIdx_295_, v___x_305_);
lean_dec(v_nextIdx_295_);
lean_inc(v___x_304_);
lean_inc(v_a_294_);
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_296_, v_a_294_, v___x_304_);
v___x_308_ = lean_array_push(v_paramNames_297_, v_a_294_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 2, v___x_308_);
lean_ctor_set(v___x_300_, 1, v___x_307_);
lean_ctor_set(v___x_300_, 0, v___x_306_);
v___x_310_ = v___x_300_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v___x_308_);
v___x_310_ = v_reuseFailAlloc_312_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_304_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
return v___x_311_;
}
}
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; 
lean_dec(v_a_294_);
v_val_317_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___x_298_, 1);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_val_317_);
lean_ctor_set(v___x_318_, 1, v_a_216_);
return v___x_318_;
}
}
default: 
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref_known(v_u_215_, 1);
v___x_319_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_320_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_319_, v_a_216_);
return v___x_320_;
}
}
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_u_215_);
lean_ctor_set(v___x_321_, 1, v_a_216_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_322_, lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_323_, v_a_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_326_, lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_326_, v_m_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_m_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_330_, lean_object* v_m_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_331_, v_a_332_, v_b_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_335_, lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_336_, v_x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_339_, lean_object* v_a_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_339_, v_a_340_, v_x_341_);
lean_dec(v_x_341_);
lean_dec(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_343_, lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_347_, lean_object* v_a_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_347_, v_a_348_, v_x_349_);
lean_dec(v_x_349_);
lean_dec(v_a_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_352_, lean_object* v_data_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_355_, lean_object* v_a_356_, lean_object* v_b_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_356_, v_b_357_, v_x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_360_, lean_object* v_i_361_, lean_object* v_source_362_, lean_object* v_target_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_361_, v_source_362_, v_target_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_4892__overap_393_; lean_object* v___x_394_; 
v___f_371_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_372_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___f_371_);
lean_ctor_set(v___x_378_, 1, v___f_372_);
v___x_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___f_373_);
lean_ctor_set(v___x_379_, 2, v___f_374_);
lean_ctor_set(v___x_379_, 3, v___f_375_);
lean_ctor_set(v___x_379_, 4, v___f_376_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___f_377_);
lean_inc_ref_n(v___x_380_, 6);
v___f_381_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_381_, 0, v___x_380_);
v___f_382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_382_, 0, v___x_380_);
v___f_383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_383_, 0, v___x_380_);
v___f_384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_384_, 0, v___x_380_);
v___x_385_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_385_, 0, lean_box(0));
lean_closure_set(v___x_385_, 1, lean_box(0));
lean_closure_set(v___x_385_, 2, v___x_380_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___f_381_);
v___x_387_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_387_, 0, lean_box(0));
lean_closure_set(v___x_387_, 1, lean_box(0));
lean_closure_set(v___x_387_, 2, v___x_380_);
v___x_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_ctor_set(v___x_388_, 2, v___f_382_);
lean_ctor_set(v___x_388_, 3, v___f_383_);
lean_ctor_set(v___x_388_, 4, v___f_384_);
v___x_389_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, lean_box(0));
lean_closure_set(v___x_389_, 2, v___x_380_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_instInhabitedExpr;
v___x_392_ = l_instInhabitedOfMonad___redArg(v___x_390_, v___x_391_);
v___x_4892__overap_393_ = lean_panic_fn_borrowed(v___x_392_, v_msg_369_);
lean_dec(v___x_392_);
v___x_394_ = lean_apply_1(v___x_4892__overap_393_, v___y_370_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v___y_397_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = l_List_reverse___redArg(v_x_396_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___y_397_);
return v___x_399_;
}
else
{
lean_object* v_head_400_; lean_object* v_tail_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_412_; 
v_head_400_ = lean_ctor_get(v_x_395_, 0);
v_tail_401_ = lean_ctor_get(v_x_395_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_403_ = v_x_395_;
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_tail_401_);
lean_inc(v_head_400_);
lean_dec(v_x_395_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; 
v___x_405_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_400_, v___y_397_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
v_snd_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v___x_405_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_x_396_);
lean_ctor_set(v___x_403_, 0, v_fst_406_);
v___x_409_ = v___x_403_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_x_396_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
v_x_395_ = v_tail_401_;
v_x_396_ = v___x_409_;
v___y_397_ = v_snd_407_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_414_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_415_ = lean_unsigned_to_nat(26u);
v___x_416_ = lean_unsigned_to_nat(79u);
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_418_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_419_ = l_mkPanicMessageWithDecl(v___x_418_, v___x_417_, v___x_416_, v___x_415_, v___x_414_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_420_, lean_object* v_a_421_){
_start:
{
uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_Expr_hasLevelParam(v_e_420_);
v___x_423_ = lean_bool_not(v___x_422_);
if (v___x_423_ == 0)
{
switch(lean_obj_tag(v_e_420_))
{
case 4:
{
lean_object* v_declName_424_; lean_object* v_us_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_declName_424_ = lean_ctor_get(v_e_420_, 0);
v_us_425_ = lean_ctor_get(v_e_420_, 1);
v___x_426_ = lean_box(0);
lean_inc(v_us_425_);
v___x_427_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_425_, v___x_426_, v_a_421_);
v_fst_428_ = lean_ctor_get(v___x_427_, 0);
v_snd_429_ = lean_ctor_get(v___x_427_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v___x_427_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
lean_dec(v___x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = l_ptrEqList___redArg(v_us_425_, v_fst_428_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_inc(v_declName_424_);
lean_dec_ref_known(v_e_420_, 2);
v___x_434_ = l_Lean_Expr_const___override(v_declName_424_, v_fst_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_434_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_snd_429_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_439_; 
lean_dec(v_fst_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v_e_420_);
v___x_439_ = v___x_431_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_snd_429_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
case 3:
{
lean_object* v_u_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_459_; 
v_u_442_ = lean_ctor_get(v_e_420_, 0);
lean_inc(v_u_442_);
v___x_443_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_442_, v_a_421_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_459_ == 0)
{
v___x_447_ = v___x_443_;
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v___x_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_459_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_u_442_);
v___x_450_ = lean_ptr_addr(v_fst_444_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_dec_ref_known(v_e_420_, 1);
v___x_452_ = l_Lean_Expr_sort___override(v_fst_444_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_452_);
v___x_454_ = v___x_447_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_snd_445_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec(v_fst_444_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v_e_420_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_snd_445_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
case 5:
{
lean_object* v_fn_460_; lean_object* v_arg_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_486_; 
v_fn_460_ = lean_ctor_get(v_e_420_, 0);
v_arg_461_ = lean_ctor_get(v_e_420_, 1);
lean_inc_ref(v_fn_460_);
v___x_462_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_460_, v_a_421_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_fst_463_);
v_snd_464_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_snd_464_);
lean_dec_ref(v___x_462_);
lean_inc_ref(v_arg_461_);
v___x_465_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_461_, v_snd_464_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_486_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_486_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_486_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___y_472_; size_t v___x_480_; size_t v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_ptr_addr(v_fn_460_);
v___x_481_ = lean_ptr_addr(v_fst_463_);
v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
v___y_472_ = v___x_482_;
goto v___jp_471_;
}
else
{
size_t v___x_483_; size_t v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_ptr_addr(v_arg_461_);
v___x_484_ = lean_ptr_addr(v_fst_466_);
v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
v___y_472_ = v___x_485_;
goto v___jp_471_;
}
v___jp_471_:
{
if (v___y_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_475_; 
lean_dec_ref_known(v_e_420_, 2);
v___x_473_ = l_Lean_Expr_app___override(v_fst_463_, v_fst_466_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_473_);
v___x_475_ = v___x_469_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_467_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_478_; 
lean_dec(v_fst_466_);
lean_dec(v_fst_463_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_e_420_);
v___x_478_ = v___x_469_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_snd_467_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_487_; lean_object* v_type_488_; lean_object* v_value_489_; lean_object* v_body_490_; uint8_t v_nondep_491_; lean_object* v___x_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; lean_object* v___x_498_; lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_526_; 
v_declName_487_ = lean_ctor_get(v_e_420_, 0);
v_type_488_ = lean_ctor_get(v_e_420_, 1);
v_value_489_ = lean_ctor_get(v_e_420_, 2);
v_body_490_ = lean_ctor_get(v_e_420_, 3);
v_nondep_491_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_488_);
v___x_492_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_488_, v_a_421_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v___x_492_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_492_);
lean_inc_ref(v_value_489_);
v___x_495_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_489_, v_snd_494_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_495_);
lean_inc_ref(v_body_490_);
v___x_498_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_490_, v_snd_497_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
v_snd_500_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_526_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_526_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_snd_500_);
lean_inc(v_fst_499_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_526_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___y_505_; size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v_type_488_);
v___x_521_ = lean_ptr_addr(v_fst_493_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
v___y_505_ = v___x_522_;
goto v___jp_504_;
}
else
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_value_489_);
v___x_524_ = lean_ptr_addr(v_fst_496_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
v___y_505_ = v___x_525_;
goto v___jp_504_;
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_inc(v_declName_487_);
lean_dec_ref_known(v_e_420_, 4);
v___x_506_ = l_Lean_Expr_letE___override(v_declName_487_, v_fst_493_, v_fst_496_, v_fst_499_, v_nondep_491_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_506_);
v___x_508_ = v___x_502_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_snd_500_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_ptr_addr(v_body_490_);
v___x_511_ = lean_ptr_addr(v_fst_499_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_inc(v_declName_487_);
lean_dec_ref_known(v_e_420_, 4);
v___x_513_ = l_Lean_Expr_letE___override(v_declName_487_, v_fst_493_, v_fst_496_, v_fst_499_, v_nondep_491_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_513_);
v___x_515_ = v___x_502_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_500_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_fst_499_);
lean_dec(v_fst_496_);
lean_dec(v_fst_493_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_e_420_);
v___x_518_ = v___x_502_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_snd_500_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_527_; lean_object* v_binderType_528_; lean_object* v_body_529_; uint8_t v_binderInfo_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_560_; 
v_binderName_527_ = lean_ctor_get(v_e_420_, 0);
v_binderType_528_ = lean_ctor_get(v_e_420_, 1);
v_body_529_ = lean_ctor_get(v_e_420_, 2);
v_binderInfo_530_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_528_);
v___x_531_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_528_, v_a_421_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
lean_inc_ref(v_body_529_);
v___x_534_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_529_, v_snd_533_);
v_fst_535_ = lean_ctor_get(v___x_534_, 0);
v_snd_536_ = lean_ctor_get(v___x_534_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_560_ == 0)
{
v___x_538_ = v___x_534_;
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_535_);
lean_dec(v___x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_560_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___y_541_; size_t v___x_554_; size_t v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_ptr_addr(v_binderType_528_);
v___x_555_ = lean_ptr_addr(v_fst_532_);
v___x_556_ = lean_usize_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
v___y_541_ = v___x_556_;
goto v___jp_540_;
}
else
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_ptr_addr(v_body_529_);
v___x_558_ = lean_ptr_addr(v_fst_535_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
v___y_541_ = v___x_559_;
goto v___jp_540_;
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc(v_binderName_527_);
lean_dec_ref_known(v_e_420_, 3);
v___x_542_ = l_Lean_Expr_forallE___override(v_binderName_527_, v_fst_532_, v_fst_535_, v_binderInfo_530_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_544_ = v___x_538_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_snd_536_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_530_, v_binderInfo_530_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
lean_inc(v_binderName_527_);
lean_dec_ref_known(v_e_420_, 3);
v___x_547_ = l_Lean_Expr_forallE___override(v_binderName_527_, v_fst_532_, v_fst_535_, v_binderInfo_530_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_547_);
v___x_549_ = v___x_538_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_snd_536_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v___x_552_; 
lean_dec(v_fst_535_);
lean_dec(v_fst_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v_e_420_);
v___x_552_ = v___x_538_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_snd_536_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_561_; lean_object* v_binderType_562_; lean_object* v_body_563_; uint8_t v_binderInfo_564_; lean_object* v___x_565_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_568_; lean_object* v_fst_569_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_594_; 
v_binderName_561_ = lean_ctor_get(v_e_420_, 0);
v_binderType_562_ = lean_ctor_get(v_e_420_, 1);
v_body_563_ = lean_ctor_get(v_e_420_, 2);
v_binderInfo_564_ = lean_ctor_get_uint8(v_e_420_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_562_);
v___x_565_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_562_, v_a_421_);
v_fst_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_fst_566_);
v_snd_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc(v_snd_567_);
lean_dec_ref(v___x_565_);
lean_inc_ref(v_body_563_);
v___x_568_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_563_, v_snd_567_);
v_fst_569_ = lean_ctor_get(v___x_568_, 0);
v_snd_570_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_594_ == 0)
{
v___x_572_ = v___x_568_;
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_inc(v_fst_569_);
lean_dec(v___x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_594_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
uint8_t v___y_575_; size_t v___x_588_; size_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_ptr_addr(v_binderType_562_);
v___x_589_ = lean_ptr_addr(v_fst_566_);
v___x_590_ = lean_usize_dec_eq(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
v___y_575_ = v___x_590_;
goto v___jp_574_;
}
else
{
size_t v___x_591_; size_t v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_ptr_addr(v_body_563_);
v___x_592_ = lean_ptr_addr(v_fst_569_);
v___x_593_ = lean_usize_dec_eq(v___x_591_, v___x_592_);
v___y_575_ = v___x_593_;
goto v___jp_574_;
}
v___jp_574_:
{
if (v___y_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_binderName_561_);
lean_dec_ref_known(v_e_420_, 3);
v___x_576_ = l_Lean_Expr_lam___override(v_binderName_561_, v_fst_566_, v_fst_569_, v_binderInfo_564_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_576_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_570_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
uint8_t v___x_580_; 
v___x_580_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_564_, v_binderInfo_564_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc(v_binderName_561_);
lean_dec_ref_known(v_e_420_, 3);
v___x_581_ = l_Lean_Expr_lam___override(v_binderName_561_, v_fst_566_, v_fst_569_, v_binderInfo_564_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_581_);
v___x_583_ = v___x_572_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_snd_570_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v_fst_569_);
lean_dec(v_fst_566_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_e_420_);
v___x_586_ = v___x_572_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_570_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_595_; lean_object* v_expr_596_; lean_object* v___x_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_613_; 
v_data_595_ = lean_ctor_get(v_e_420_, 0);
v_expr_596_ = lean_ctor_get(v_e_420_, 1);
lean_inc_ref(v_expr_596_);
v___x_597_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_596_, v_a_421_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
v_snd_599_ = lean_ctor_get(v___x_597_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_613_ == 0)
{
v___x_601_ = v___x_597_;
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snd_599_);
lean_inc(v_fst_598_);
lean_dec(v___x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_613_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
size_t v___x_603_; size_t v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_ptr_addr(v_expr_596_);
v___x_604_ = lean_ptr_addr(v_fst_598_);
v___x_605_ = lean_usize_dec_eq(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_inc(v_data_595_);
lean_dec_ref_known(v_e_420_, 2);
v___x_606_ = l_Lean_Expr_mdata___override(v_data_595_, v_fst_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_606_);
v___x_608_ = v___x_601_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_snd_599_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_object* v___x_611_; 
lean_dec(v_fst_598_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_e_420_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_599_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
case 11:
{
lean_object* v_typeName_614_; lean_object* v_idx_615_; lean_object* v_struct_616_; lean_object* v___x_617_; lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_typeName_614_ = lean_ctor_get(v_e_420_, 0);
v_idx_615_ = lean_ctor_get(v_e_420_, 1);
v_struct_616_ = lean_ctor_get(v_e_420_, 2);
lean_inc_ref(v_struct_616_);
v___x_617_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_616_, v_a_421_);
v_fst_618_ = lean_ctor_get(v___x_617_, 0);
v_snd_619_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v___x_617_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
lean_dec(v___x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
size_t v___x_623_; size_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_ptr_addr(v_struct_616_);
v___x_624_ = lean_ptr_addr(v_fst_618_);
v___x_625_ = lean_usize_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc(v_idx_615_);
lean_inc(v_typeName_614_);
lean_dec_ref_known(v_e_420_, 3);
v___x_626_ = l_Lean_Expr_proj___override(v_typeName_614_, v_idx_615_, v_fst_618_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_626_);
v___x_628_ = v___x_621_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_619_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_fst_618_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_420_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_e_420_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_snd_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
case 2:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref_known(v_e_420_, 1);
v___x_634_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_635_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_634_, v_a_421_);
return v___x_635_;
}
default: 
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_e_420_);
lean_ctor_set(v___x_636_, 1, v_a_421_);
return v___x_636_;
}
}
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_e_420_);
lean_ctor_set(v___x_637_, 1, v_a_421_);
return v___x_637_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = lean_unsigned_to_nat(16u);
v___x_640_ = lean_mk_array(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_646_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_647_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
lean_ctor_set(v___x_649_, 2, v___x_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_snd_653_; lean_object* v_fst_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_663_; 
v___x_651_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_652_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_650_, v___x_651_);
v_snd_653_ = lean_ctor_get(v___x_652_, 1);
v_fst_654_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_663_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snd_653_);
lean_inc(v_fst_654_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_663_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_paramNames_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_paramNames_658_ = lean_ctor_get(v_snd_653_, 2);
lean_inc_ref(v_paramNames_658_);
lean_dec(v_snd_653_);
v___x_659_ = lean_array_to_list(v_paramNames_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_CollectLevelParams_visitExpr(v_type_664_, v_a_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_667_, lean_object* v_a_668_){
_start:
{
if (lean_obj_tag(v_arg_667_) == 2)
{
lean_object* v_expr_669_; lean_object* v___x_670_; 
v_expr_669_ = lean_ctor_get(v_arg_667_, 0);
lean_inc_ref(v_expr_669_);
lean_dec_ref_known(v_arg_667_, 1);
v___x_670_ = l_Lean_CollectLevelParams_visitExpr(v_expr_669_, v_a_668_);
return v___x_670_;
}
else
{
lean_dec(v_arg_667_);
return v_a_668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_671_, size_t v_i_672_, size_t v_stop_673_, lean_object* v_b_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_eq(v_i_672_, v_stop_673_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; 
v___x_676_ = lean_array_uget_borrowed(v_as_671_, v_i_672_);
lean_inc(v___x_676_);
v___x_677_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_676_, v_b_674_);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_672_, v___x_678_);
v_i_672_ = v___x_679_;
v_b_674_ = v___x_677_;
goto _start;
}
else
{
return v_b_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_681_, lean_object* v_i_682_, lean_object* v_stop_683_, lean_object* v_b_684_){
_start:
{
size_t v_i_boxed_685_; size_t v_stop_boxed_686_; lean_object* v_res_687_; 
v_i_boxed_685_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_stop_boxed_686_ = lean_unbox_usize(v_stop_683_);
lean_dec(v_stop_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_681_, v_i_boxed_685_, v_stop_boxed_686_, v_b_684_);
lean_dec_ref(v_as_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_688_, lean_object* v_s_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_args_688_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
return v_s_689_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = lean_nat_dec_le(v___x_691_, v___x_691_);
if (v___x_693_ == 0)
{
if (v___x_692_ == 0)
{
return v_s_689_;
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_691_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_688_, v___x_694_, v___x_695_, v_s_689_);
return v___x_696_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_691_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_688_, v___x_697_, v___x_698_, v_s_689_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_700_, lean_object* v_s_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_700_, v_s_701_);
lean_dec_ref(v_args_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_703_, lean_object* v_a_704_){
_start:
{
switch(lean_obj_tag(v_e_703_))
{
case 3:
{
lean_object* v_us_705_; lean_object* v_args_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_us_705_ = lean_ctor_get(v_e_703_, 1);
lean_inc(v_us_705_);
v_args_706_ = lean_ctor_get(v_e_703_, 2);
lean_inc_ref(v_args_706_);
lean_dec_ref_known(v_e_703_, 3);
v___x_707_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_706_, v_a_704_);
lean_dec_ref(v_args_706_);
v___x_708_ = l_Lean_CollectLevelParams_visitLevels(v_us_705_, v___x_707_);
return v___x_708_;
}
case 4:
{
lean_object* v_args_709_; lean_object* v___x_710_; 
v_args_709_ = lean_ctor_get(v_e_703_, 1);
lean_inc_ref(v_args_709_);
lean_dec_ref_known(v_e_703_, 2);
v___x_710_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_709_, v_a_704_);
lean_dec_ref(v_args_709_);
return v___x_710_;
}
default: 
{
lean_dec(v_e_703_);
return v_a_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_type_713_; lean_object* v___x_714_; 
v_type_713_ = lean_ctor_get(v_p_711_, 2);
lean_inc_ref(v_type_713_);
lean_dec_ref(v_p_711_);
v___x_714_ = l_Lean_CollectLevelParams_visitExpr(v_type_713_, v_a_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_715_, size_t v_i_716_, size_t v_stop_717_, lean_object* v_b_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_eq(v_i_716_, v_stop_717_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; 
v___x_720_ = lean_array_uget_borrowed(v_as_715_, v_i_716_);
lean_inc(v___x_720_);
v___x_721_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_720_, v_b_718_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_716_, v___x_722_);
v_i_716_ = v___x_723_;
v_b_718_ = v___x_721_;
goto _start;
}
else
{
return v_b_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_725_, lean_object* v_i_726_, lean_object* v_stop_727_, lean_object* v_b_728_){
_start:
{
size_t v_i_boxed_729_; size_t v_stop_boxed_730_; lean_object* v_res_731_; 
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_stop_boxed_730_ = lean_unbox_usize(v_stop_727_);
lean_dec(v_stop_727_);
v_res_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_725_, v_i_boxed_729_, v_stop_boxed_730_, v_b_728_);
lean_dec_ref(v_as_725_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_732_, lean_object* v_s_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_array_get_size(v_ps_732_);
v___x_736_ = lean_nat_dec_lt(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
return v_s_733_;
}
else
{
uint8_t v___x_737_; 
v___x_737_ = lean_nat_dec_le(v___x_735_, v___x_735_);
if (v___x_737_ == 0)
{
if (v___x_736_ == 0)
{
return v_s_733_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_735_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_732_, v___x_738_, v___x_739_, v_s_733_);
return v___x_740_;
}
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_735_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_732_, v___x_741_, v___x_742_, v_s_733_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_744_, lean_object* v_s_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_744_, v_s_745_);
lean_dec_ref(v_ps_744_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_747_, size_t v_i_748_, size_t v_stop_749_, lean_object* v_b_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_eq(v_i_748_, v_stop_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; 
v___x_752_ = lean_array_uget_borrowed(v_as_747_, v_i_748_);
lean_inc(v___x_752_);
v___x_753_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_752_, v_b_750_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_748_, v___x_754_);
v_i_748_ = v___x_755_;
v_b_750_ = v___x_753_;
goto _start;
}
else
{
return v_b_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_757_, lean_object* v_s_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v_alts_757_);
v___x_761_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_761_ == 0)
{
return v_s_758_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = lean_nat_dec_le(v___x_760_, v___x_760_);
if (v___x_762_ == 0)
{
if (v___x_761_ == 0)
{
return v_s_758_;
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_760_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_757_, v___x_763_, v___x_764_, v_s_758_);
return v___x_765_;
}
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_760_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_757_, v___x_766_, v___x_767_, v_s_758_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_769_, lean_object* v_a_770_){
_start:
{
switch(lean_obj_tag(v_x_769_))
{
case 0:
{
lean_object* v_decl_771_; lean_object* v_k_772_; lean_object* v_type_773_; lean_object* v_value_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_decl_771_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_decl_771_);
v_k_772_ = lean_ctor_get(v_x_769_, 1);
lean_inc_ref(v_k_772_);
lean_dec_ref_known(v_x_769_, 2);
v_type_773_ = lean_ctor_get(v_decl_771_, 2);
lean_inc_ref(v_type_773_);
v_value_774_ = lean_ctor_get(v_decl_771_, 3);
lean_inc(v_value_774_);
lean_dec_ref(v_decl_771_);
v___x_775_ = l_Lean_CollectLevelParams_visitExpr(v_type_773_, v_a_770_);
v___x_776_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_774_, v___x_775_);
v_x_769_ = v_k_772_;
v_a_770_ = v___x_776_;
goto _start;
}
case 3:
{
lean_object* v_args_778_; lean_object* v___x_779_; 
v_args_778_ = lean_ctor_get(v_x_769_, 1);
lean_inc_ref(v_args_778_);
lean_dec_ref_known(v_x_769_, 2);
v___x_779_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_778_, v_a_770_);
lean_dec_ref(v_args_778_);
return v___x_779_;
}
case 4:
{
lean_object* v_cases_780_; lean_object* v_resultType_781_; lean_object* v_alts_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_cases_780_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_cases_780_);
lean_dec_ref_known(v_x_769_, 1);
v_resultType_781_ = lean_ctor_get(v_cases_780_, 1);
lean_inc_ref(v_resultType_781_);
v_alts_782_ = lean_ctor_get(v_cases_780_, 3);
lean_inc_ref(v_alts_782_);
lean_dec_ref(v_cases_780_);
v___x_783_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_781_, v_a_770_);
v___x_784_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_782_, v___x_783_);
lean_dec_ref(v_alts_782_);
return v___x_784_;
}
case 5:
{
lean_dec_ref_known(v_x_769_, 1);
return v_a_770_;
}
case 6:
{
lean_object* v_type_785_; lean_object* v___x_786_; 
v_type_785_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_type_785_);
lean_dec_ref_known(v_x_769_, 1);
v___x_786_ = l_Lean_CollectLevelParams_visitExpr(v_type_785_, v_a_770_);
return v___x_786_;
}
default: 
{
lean_object* v_decl_787_; lean_object* v_k_788_; lean_object* v_params_789_; lean_object* v_type_790_; lean_object* v_value_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_decl_787_ = lean_ctor_get(v_x_769_, 0);
lean_inc_ref(v_decl_787_);
v_k_788_ = lean_ctor_get(v_x_769_, 1);
lean_inc_ref(v_k_788_);
lean_dec_ref(v_x_769_);
v_params_789_ = lean_ctor_get(v_decl_787_, 2);
lean_inc_ref(v_params_789_);
v_type_790_ = lean_ctor_get(v_decl_787_, 3);
lean_inc_ref(v_type_790_);
v_value_791_ = lean_ctor_get(v_decl_787_, 4);
lean_inc_ref(v_value_791_);
lean_dec_ref(v_decl_787_);
v___x_792_ = l_Lean_CollectLevelParams_visitExpr(v_type_790_, v_a_770_);
v___x_793_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_789_, v___x_792_);
lean_dec_ref(v_params_789_);
v___x_794_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_791_, v___x_793_);
v_x_769_ = v_k_788_;
v_a_770_ = v___x_794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_796_, lean_object* v_a_797_){
_start:
{
if (lean_obj_tag(v_alt_796_) == 0)
{
lean_object* v_params_798_; lean_object* v_code_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_params_798_ = lean_ctor_get(v_alt_796_, 1);
lean_inc_ref(v_params_798_);
v_code_799_ = lean_ctor_get(v_alt_796_, 2);
lean_inc_ref(v_code_799_);
lean_dec_ref_known(v_alt_796_, 3);
v___x_800_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_798_, v_a_797_);
lean_dec_ref(v_params_798_);
v___x_801_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_799_, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v_code_802_; lean_object* v___x_803_; 
v_code_802_ = lean_ctor_get(v_alt_796_, 0);
lean_inc_ref(v_code_802_);
lean_dec_ref_known(v_alt_796_, 1);
v___x_803_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_802_, v_a_797_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_804_, lean_object* v_i_805_, lean_object* v_stop_806_, lean_object* v_b_807_){
_start:
{
size_t v_i_boxed_808_; size_t v_stop_boxed_809_; lean_object* v_res_810_; 
v_i_boxed_808_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_stop_boxed_809_ = lean_unbox_usize(v_stop_806_);
lean_dec(v_stop_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_804_, v_i_boxed_808_, v_stop_boxed_809_, v_b_807_);
lean_dec_ref(v_as_804_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_811_, lean_object* v_s_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_811_, v_s_812_);
lean_dec_ref(v_alts_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_814_, lean_object* v_a_815_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v_code_816_; lean_object* v___x_817_; 
v_code_816_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref(v_code_816_);
lean_dec_ref_known(v_x_814_, 1);
v___x_817_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_816_, v_a_815_);
return v___x_817_;
}
else
{
lean_dec_ref_known(v_x_814_, 1);
return v_a_815_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_unsigned_to_nat(16u);
v___x_820_ = lean_mk_array(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_825_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
lean_ctor_set(v___x_826_, 2, v___x_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_827_){
_start:
{
lean_object* v_toSignature_828_; lean_object* v_value_829_; uint8_t v_recursive_830_; lean_object* v_inlineAttr_x3f_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_856_; 
v_toSignature_828_ = lean_ctor_get(v_decl_827_, 0);
v_value_829_ = lean_ctor_get(v_decl_827_, 1);
v_recursive_830_ = lean_ctor_get_uint8(v_decl_827_, sizeof(void*)*3);
v_inlineAttr_x3f_831_ = lean_ctor_get(v_decl_827_, 2);
v_isSharedCheck_856_ = !lean_is_exclusive(v_decl_827_);
if (v_isSharedCheck_856_ == 0)
{
v___x_833_ = v_decl_827_;
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_inlineAttr_x3f_831_);
lean_inc(v_value_829_);
lean_inc(v_toSignature_828_);
lean_dec(v_decl_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_name_835_; lean_object* v_type_836_; lean_object* v_params_837_; uint8_t v_safe_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_854_; 
v_name_835_ = lean_ctor_get(v_toSignature_828_, 0);
v_type_836_ = lean_ctor_get(v_toSignature_828_, 2);
v_params_837_ = lean_ctor_get(v_toSignature_828_, 3);
v_safe_838_ = lean_ctor_get_uint8(v_toSignature_828_, sizeof(void*)*4);
v_isSharedCheck_854_ = !lean_is_exclusive(v_toSignature_828_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_toSignature_828_, 1);
lean_dec(v_unused_855_);
v___x_840_ = v_toSignature_828_;
v_isShared_841_ = v_isSharedCheck_854_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_params_837_);
lean_inc(v_type_836_);
lean_inc(v_name_835_);
lean_dec(v_toSignature_828_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_854_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_params_846_; lean_object* v_levelParams_847_; lean_object* v___x_849_; 
v___x_842_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_836_);
v___x_843_ = l_Lean_CollectLevelParams_visitExpr(v_type_836_, v___x_842_);
v___x_844_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_837_, v___x_843_);
lean_inc_ref(v_value_829_);
v___x_845_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_829_, v___x_844_);
v_params_846_ = lean_ctor_get(v___x_845_, 2);
lean_inc_ref(v_params_846_);
lean_dec_ref(v___x_845_);
v_levelParams_847_ = lean_array_to_list(v_params_846_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_levelParams_847_);
v___x_849_ = v___x_840_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_name_835_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_levelParams_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_type_836_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_params_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, sizeof(void*)*4, v_safe_838_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_849_);
v___x_851_ = v___x_833_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_value_829_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_inlineAttr_x3f_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_852_, sizeof(void*)*3, v_recursive_830_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
