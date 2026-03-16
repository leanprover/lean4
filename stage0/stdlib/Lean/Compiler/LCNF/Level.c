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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_inc_ref(v___x_19_);
v___f_20_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_20_, 0, v___x_19_);
lean_inc_ref(v___x_19_);
v___f_21_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_21_, 0, v___x_19_);
lean_inc_ref(v___x_19_);
v___f_22_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_22_, 0, v___x_19_);
lean_inc_ref(v___x_19_);
v___f_23_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_23_, 0, v___x_19_);
lean_inc_ref(v___x_19_);
v___x_24_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_24_, 0, lean_box(0));
lean_closure_set(v___x_24_, 1, lean_box(0));
lean_closure_set(v___x_24_, 2, v___x_19_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___f_20_);
lean_inc_ref(v___x_19_);
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
v___x_3193__overap_32_ = lean_panic_fn(v___x_31_, v_msg_8_);
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
uint8_t v___x_217_; 
v___x_217_ = l_Lean_Level_hasParam(v_u_215_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_u_215_);
lean_ctor_set(v___x_218_, 1, v_a_216_);
return v___x_218_;
}
else
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v_u_215_);
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
lean_dec_ref(v___x_298_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_val_317_);
lean_ctor_set(v___x_318_, 1, v_a_216_);
return v___x_318_;
}
}
default: 
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_u_215_);
v___x_319_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_320_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_319_, v_a_216_);
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_321_, lean_object* v_m_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_322_, v_a_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_325_, lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_325_, v_m_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_m_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_329_, lean_object* v_m_330_, lean_object* v_a_331_, lean_object* v_b_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_330_, v_a_331_, v_b_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_334_, lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_335_, v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_338_, lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_338_, v_a_339_, v_x_340_);
lean_dec(v_x_340_);
lean_dec(v_a_339_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_342_, lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_343_, v_x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_346_, lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_346_, v_a_347_, v_x_348_);
lean_dec(v_x_348_);
lean_dec(v_a_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_351_, lean_object* v_data_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_354_, lean_object* v_a_355_, lean_object* v_b_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_355_, v_b_356_, v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_359_, lean_object* v_i_360_, lean_object* v_source_361_, lean_object* v_target_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_360_, v_source_361_, v_target_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_365_, v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_5181__overap_392_; lean_object* v___x_393_; 
v___f_370_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_371_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_372_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___f_370_);
lean_ctor_set(v___x_377_, 1, v___f_371_);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___f_372_);
lean_ctor_set(v___x_378_, 2, v___f_373_);
lean_ctor_set(v___x_378_, 3, v___f_374_);
lean_ctor_set(v___x_378_, 4, v___f_375_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___f_376_);
lean_inc_ref(v___x_379_);
v___f_380_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_380_, 0, v___x_379_);
lean_inc_ref(v___x_379_);
v___f_381_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_381_, 0, v___x_379_);
lean_inc_ref(v___x_379_);
v___f_382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_382_, 0, v___x_379_);
lean_inc_ref(v___x_379_);
v___f_383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_383_, 0, v___x_379_);
lean_inc_ref(v___x_379_);
v___x_384_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, lean_box(0));
lean_closure_set(v___x_384_, 2, v___x_379_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___f_380_);
lean_inc_ref(v___x_379_);
v___x_386_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_386_, 0, lean_box(0));
lean_closure_set(v___x_386_, 1, lean_box(0));
lean_closure_set(v___x_386_, 2, v___x_379_);
v___x_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
lean_ctor_set(v___x_387_, 2, v___f_381_);
lean_ctor_set(v___x_387_, 3, v___f_382_);
lean_ctor_set(v___x_387_, 4, v___f_383_);
v___x_388_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_388_, 0, lean_box(0));
lean_closure_set(v___x_388_, 1, lean_box(0));
lean_closure_set(v___x_388_, 2, v___x_379_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_instInhabitedExpr;
v___x_391_ = l_instInhabitedOfMonad___redArg(v___x_389_, v___x_390_);
v___x_5181__overap_392_ = lean_panic_fn(v___x_391_, v_msg_368_);
v___x_393_ = lean_apply_1(v___x_5181__overap_392_, v___y_369_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = l_List_reverse___redArg(v_x_395_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___y_396_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_411_; 
v_head_399_ = lean_ctor_get(v_x_394_, 0);
v_tail_400_ = lean_ctor_get(v_x_394_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_402_ = v_x_394_;
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_tail_400_);
lean_inc(v_head_399_);
lean_dec(v_x_394_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_411_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; 
v___x_404_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_399_, v___y_396_);
v_fst_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_fst_405_);
v_snd_406_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_snd_406_);
lean_dec_ref(v___x_404_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v_x_395_);
lean_ctor_set(v___x_402_, 0, v_fst_405_);
v___x_408_ = v___x_402_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_fst_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_x_395_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v_x_394_ = v_tail_400_;
v_x_395_ = v___x_408_;
v___y_396_ = v_snd_406_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_413_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_414_ = lean_unsigned_to_nat(26u);
v___x_415_ = lean_unsigned_to_nat(79u);
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_418_ = l_mkPanicMessageWithDecl(v___x_417_, v___x_416_, v___x_415_, v___x_414_, v___x_413_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = l_Lean_Expr_hasLevelParam(v_e_419_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_e_419_);
lean_ctor_set(v___x_422_, 1, v_a_420_);
return v___x_422_;
}
else
{
switch(lean_obj_tag(v_e_419_))
{
case 4:
{
lean_object* v_declName_423_; lean_object* v_us_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_440_; 
v_declName_423_ = lean_ctor_get(v_e_419_, 0);
v_us_424_ = lean_ctor_get(v_e_419_, 1);
v___x_425_ = lean_box(0);
lean_inc(v_us_424_);
v___x_426_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_424_, v___x_425_, v_a_420_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_440_ == 0)
{
v___x_430_ = v___x_426_;
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_snd_428_);
lean_inc(v_fst_427_);
lean_dec(v___x_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; 
v___x_432_ = l_ptrEqList___redArg(v_us_424_, v_fst_427_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_declName_423_);
lean_dec_ref(v_e_419_);
v___x_433_ = l_Lean_Expr_const___override(v_declName_423_, v_fst_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_433_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_snd_428_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; 
lean_dec(v_fst_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_e_419_);
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_428_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
case 3:
{
lean_object* v_u_441_; lean_object* v___x_442_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_458_; 
v_u_441_ = lean_ctor_get(v_e_419_, 0);
lean_inc(v_u_441_);
v___x_442_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_441_, v_a_420_);
v_fst_443_ = lean_ctor_get(v___x_442_, 0);
v_snd_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_458_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_458_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_458_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
size_t v___x_448_; size_t v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_ptr_addr(v_u_441_);
v___x_449_ = lean_ptr_addr(v_fst_443_);
v___x_450_ = lean_usize_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_dec_ref(v_e_419_);
v___x_451_ = l_Lean_Expr_sort___override(v_fst_443_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_451_);
v___x_453_ = v___x_446_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_snd_444_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_fst_443_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_e_419_);
v___x_456_ = v___x_446_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_444_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
case 5:
{
lean_object* v_fn_459_; lean_object* v_arg_460_; lean_object* v___x_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_464_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_485_; 
v_fn_459_ = lean_ctor_get(v_e_419_, 0);
v_arg_460_ = lean_ctor_get(v_e_419_, 1);
lean_inc_ref(v_fn_459_);
v___x_461_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_459_, v_a_420_);
v_fst_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v___x_461_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v___x_461_);
lean_inc_ref(v_arg_460_);
v___x_464_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_460_, v_snd_463_);
v_fst_465_ = lean_ctor_get(v___x_464_, 0);
v_snd_466_ = lean_ctor_get(v___x_464_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_485_ == 0)
{
v___x_468_ = v___x_464_;
v_isShared_469_ = v_isSharedCheck_485_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v___x_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_485_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint8_t v___y_471_; size_t v___x_479_; size_t v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_ptr_addr(v_fn_459_);
v___x_480_ = lean_ptr_addr(v_fst_462_);
v___x_481_ = lean_usize_dec_eq(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
v___y_471_ = v___x_481_;
goto v___jp_470_;
}
else
{
size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_ptr_addr(v_arg_460_);
v___x_483_ = lean_ptr_addr(v_fst_465_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
v___y_471_ = v___x_484_;
goto v___jp_470_;
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec_ref(v_e_419_);
v___x_472_ = l_Lean_Expr_app___override(v_fst_462_, v_fst_465_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_472_);
v___x_474_ = v___x_468_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_snd_466_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
lean_object* v___x_477_; 
lean_dec(v_fst_465_);
lean_dec(v_fst_462_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v_e_419_);
v___x_477_ = v___x_468_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_466_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_486_; lean_object* v_type_487_; lean_object* v_value_488_; lean_object* v_body_489_; uint8_t v_nondep_490_; lean_object* v___x_491_; lean_object* v_fst_492_; lean_object* v_snd_493_; lean_object* v___x_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; lean_object* v___x_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_525_; 
v_declName_486_ = lean_ctor_get(v_e_419_, 0);
v_type_487_ = lean_ctor_get(v_e_419_, 1);
v_value_488_ = lean_ctor_get(v_e_419_, 2);
v_body_489_ = lean_ctor_get(v_e_419_, 3);
v_nondep_490_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_487_);
v___x_491_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_487_, v_a_420_);
v_fst_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_fst_492_);
v_snd_493_ = lean_ctor_get(v___x_491_, 1);
lean_inc(v_snd_493_);
lean_dec_ref(v___x_491_);
lean_inc_ref(v_value_488_);
v___x_494_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_488_, v_snd_493_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_496_);
lean_dec_ref(v___x_494_);
lean_inc_ref(v_body_489_);
v___x_497_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_489_, v_snd_496_);
v_fst_498_ = lean_ctor_get(v___x_497_, 0);
v_snd_499_ = lean_ctor_get(v___x_497_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_525_ == 0)
{
v___x_501_ = v___x_497_;
v_isShared_502_ = v_isSharedCheck_525_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snd_499_);
lean_inc(v_fst_498_);
lean_dec(v___x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_525_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___y_504_; size_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_ptr_addr(v_type_487_);
v___x_520_ = lean_ptr_addr(v_fst_492_);
v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
v___y_504_ = v___x_521_;
goto v___jp_503_;
}
else
{
size_t v___x_522_; size_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_ptr_addr(v_value_488_);
v___x_523_ = lean_ptr_addr(v_fst_495_);
v___x_524_ = lean_usize_dec_eq(v___x_522_, v___x_523_);
v___y_504_ = v___x_524_;
goto v___jp_503_;
}
v___jp_503_:
{
if (v___y_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_507_; 
lean_inc(v_declName_486_);
lean_dec_ref(v_e_419_);
v___x_505_ = l_Lean_Expr_letE___override(v_declName_486_, v_fst_492_, v_fst_495_, v_fst_498_, v_nondep_490_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_505_);
v___x_507_ = v___x_501_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_snd_499_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
else
{
size_t v___x_509_; size_t v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_ptr_addr(v_body_489_);
v___x_510_ = lean_ptr_addr(v_fst_498_);
v___x_511_ = lean_usize_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_514_; 
lean_inc(v_declName_486_);
lean_dec_ref(v_e_419_);
v___x_512_ = l_Lean_Expr_letE___override(v_declName_486_, v_fst_492_, v_fst_495_, v_fst_498_, v_nondep_490_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_512_);
v___x_514_ = v___x_501_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_499_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v_fst_498_);
lean_dec(v_fst_495_);
lean_dec(v_fst_492_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v_e_419_);
v___x_517_ = v___x_501_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_snd_499_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_526_; lean_object* v_binderType_527_; lean_object* v_body_528_; uint8_t v_binderInfo_529_; lean_object* v___x_530_; lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_533_; lean_object* v_fst_534_; lean_object* v_snd_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_559_; 
v_binderName_526_ = lean_ctor_get(v_e_419_, 0);
v_binderType_527_ = lean_ctor_get(v_e_419_, 1);
v_body_528_ = lean_ctor_get(v_e_419_, 2);
v_binderInfo_529_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_527_);
v___x_530_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_527_, v_a_420_);
v_fst_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_fst_531_);
v_snd_532_ = lean_ctor_get(v___x_530_, 1);
lean_inc(v_snd_532_);
lean_dec_ref(v___x_530_);
lean_inc_ref(v_body_528_);
v___x_533_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_528_, v_snd_532_);
v_fst_534_ = lean_ctor_get(v___x_533_, 0);
v_snd_535_ = lean_ctor_get(v___x_533_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_559_ == 0)
{
v___x_537_ = v___x_533_;
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_snd_535_);
lean_inc(v_fst_534_);
lean_dec(v___x_533_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_559_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___y_540_; size_t v___x_553_; size_t v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_ptr_addr(v_binderType_527_);
v___x_554_ = lean_ptr_addr(v_fst_531_);
v___x_555_ = lean_usize_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
v___y_540_ = v___x_555_;
goto v___jp_539_;
}
else
{
size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_ptr_addr(v_body_528_);
v___x_557_ = lean_ptr_addr(v_fst_534_);
v___x_558_ = lean_usize_dec_eq(v___x_556_, v___x_557_);
v___y_540_ = v___x_558_;
goto v___jp_539_;
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc(v_binderName_526_);
lean_dec_ref(v_e_419_);
v___x_541_ = l_Lean_Expr_forallE___override(v_binderName_526_, v_fst_531_, v_fst_534_, v_binderInfo_529_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_541_);
v___x_543_ = v___x_537_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_535_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
uint8_t v___x_545_; 
v___x_545_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_529_, v_binderInfo_529_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_548_; 
lean_inc(v_binderName_526_);
lean_dec_ref(v_e_419_);
v___x_546_ = l_Lean_Expr_forallE___override(v_binderName_526_, v_fst_531_, v_fst_534_, v_binderInfo_529_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_546_);
v___x_548_ = v___x_537_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_snd_535_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v___x_551_; 
lean_dec(v_fst_534_);
lean_dec(v_fst_531_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v_e_419_);
v___x_551_ = v___x_537_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_535_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_560_; lean_object* v_binderType_561_; lean_object* v_body_562_; uint8_t v_binderInfo_563_; lean_object* v___x_564_; lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_593_; 
v_binderName_560_ = lean_ctor_get(v_e_419_, 0);
v_binderType_561_ = lean_ctor_get(v_e_419_, 1);
v_body_562_ = lean_ctor_get(v_e_419_, 2);
v_binderInfo_563_ = lean_ctor_get_uint8(v_e_419_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_561_);
v___x_564_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_561_, v_a_420_);
v_fst_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_fst_565_);
v_snd_566_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_566_);
lean_dec_ref(v___x_564_);
lean_inc_ref(v_body_562_);
v___x_567_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_562_, v_snd_566_);
v_fst_568_ = lean_ctor_get(v___x_567_, 0);
v_snd_569_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_593_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_inc(v_fst_568_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_593_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
uint8_t v___y_574_; size_t v___x_587_; size_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_ptr_addr(v_binderType_561_);
v___x_588_ = lean_ptr_addr(v_fst_565_);
v___x_589_ = lean_usize_dec_eq(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
v___y_574_ = v___x_589_;
goto v___jp_573_;
}
else
{
size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_ptr_addr(v_body_562_);
v___x_591_ = lean_ptr_addr(v_fst_568_);
v___x_592_ = lean_usize_dec_eq(v___x_590_, v___x_591_);
v___y_574_ = v___x_592_;
goto v___jp_573_;
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_inc(v_binderName_560_);
lean_dec_ref(v_e_419_);
v___x_575_ = l_Lean_Expr_lam___override(v_binderName_560_, v_fst_565_, v_fst_568_, v_binderInfo_563_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_snd_569_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
else
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_563_, v_binderInfo_563_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_inc(v_binderName_560_);
lean_dec_ref(v_e_419_);
v___x_580_ = l_Lean_Expr_lam___override(v_binderName_560_, v_fst_565_, v_fst_568_, v_binderInfo_563_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_580_);
v___x_582_ = v___x_571_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_snd_569_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v_fst_568_);
lean_dec(v_fst_565_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_e_419_);
v___x_585_ = v___x_571_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_569_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_594_; lean_object* v_expr_595_; lean_object* v___x_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_612_; 
v_data_594_ = lean_ctor_get(v_e_419_, 0);
v_expr_595_ = lean_ctor_get(v_e_419_, 1);
lean_inc_ref(v_expr_595_);
v___x_596_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_595_, v_a_420_);
v_fst_597_ = lean_ctor_get(v___x_596_, 0);
v_snd_598_ = lean_ctor_get(v___x_596_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_612_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_inc(v_fst_597_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
size_t v___x_602_; size_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_ptr_addr(v_expr_595_);
v___x_603_ = lean_ptr_addr(v_fst_597_);
v___x_604_ = lean_usize_dec_eq(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_inc(v_data_594_);
lean_dec_ref(v_e_419_);
v___x_605_ = l_Lean_Expr_mdata___override(v_data_594_, v_fst_597_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_605_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_snd_598_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v___x_610_; 
lean_dec(v_fst_597_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_e_419_);
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_snd_598_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
case 11:
{
lean_object* v_typeName_613_; lean_object* v_idx_614_; lean_object* v_struct_615_; lean_object* v___x_616_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_typeName_613_ = lean_ctor_get(v_e_419_, 0);
v_idx_614_ = lean_ctor_get(v_e_419_, 1);
v_struct_615_ = lean_ctor_get(v_e_419_, 2);
lean_inc_ref(v_struct_615_);
v___x_616_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_615_, v_a_420_);
v_fst_617_ = lean_ctor_get(v___x_616_, 0);
v_snd_618_ = lean_ctor_get(v___x_616_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v___x_616_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snd_618_);
lean_inc(v_fst_617_);
lean_dec(v___x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
size_t v___x_622_; size_t v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_ptr_addr(v_struct_615_);
v___x_623_ = lean_ptr_addr(v_fst_617_);
v___x_624_ = lean_usize_dec_eq(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_idx_614_);
lean_inc(v_typeName_613_);
lean_dec_ref(v_e_419_);
v___x_625_ = l_Lean_Expr_proj___override(v_typeName_613_, v_idx_614_, v_fst_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_snd_618_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec(v_fst_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_e_419_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_e_419_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_snd_618_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
case 2:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec_ref(v_e_419_);
v___x_633_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_634_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_633_, v_a_420_);
return v___x_634_;
}
default: 
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_e_419_);
lean_ctor_set(v___x_635_, 1, v_a_420_);
return v___x_635_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_unsigned_to_nat(16u);
v___x_638_ = lean_mk_array(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_645_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_snd_651_; lean_object* v_fst_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v___x_649_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_650_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_648_, v___x_649_);
v_snd_651_ = lean_ctor_get(v___x_650_, 1);
v_fst_652_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_661_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_651_);
lean_inc(v_fst_652_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_paramNames_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_paramNames_656_ = lean_ctor_get(v_snd_651_, 2);
lean_inc_ref(v_paramNames_656_);
lean_dec(v_snd_651_);
v___x_657_ = lean_array_to_list(v_paramNames_656_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_CollectLevelParams_visitExpr(v_type_662_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_665_, lean_object* v_a_666_){
_start:
{
if (lean_obj_tag(v_arg_665_) == 2)
{
lean_object* v_expr_667_; lean_object* v___x_668_; 
v_expr_667_ = lean_ctor_get(v_arg_665_, 0);
lean_inc_ref(v_expr_667_);
lean_dec_ref(v_arg_665_);
v___x_668_ = l_Lean_CollectLevelParams_visitExpr(v_expr_667_, v_a_666_);
return v___x_668_;
}
else
{
lean_dec(v_arg_665_);
return v_a_666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_669_, size_t v_i_670_, size_t v_stop_671_, lean_object* v_b_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_eq(v_i_670_, v_stop_671_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; 
v___x_674_ = lean_array_uget_borrowed(v_as_669_, v_i_670_);
lean_inc(v___x_674_);
v___x_675_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_674_, v_b_672_);
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_670_, v___x_676_);
v_i_670_ = v___x_677_;
v_b_672_ = v___x_675_;
goto _start;
}
else
{
return v_b_672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_679_, lean_object* v_i_680_, lean_object* v_stop_681_, lean_object* v_b_682_){
_start:
{
size_t v_i_boxed_683_; size_t v_stop_boxed_684_; lean_object* v_res_685_; 
v_i_boxed_683_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_stop_boxed_684_ = lean_unbox_usize(v_stop_681_);
lean_dec(v_stop_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_679_, v_i_boxed_683_, v_stop_boxed_684_, v_b_682_);
lean_dec_ref(v_as_679_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_686_, lean_object* v_s_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_args_686_);
v___x_690_ = lean_nat_dec_lt(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
return v_s_687_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_691_ == 0)
{
if (v___x_690_ == 0)
{
return v_s_687_;
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_689_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_686_, v___x_692_, v___x_693_, v_s_687_);
return v___x_694_;
}
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_689_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_686_, v___x_695_, v___x_696_, v_s_687_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_698_, lean_object* v_s_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_698_, v_s_699_);
lean_dec_ref(v_args_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_701_, lean_object* v_a_702_){
_start:
{
switch(lean_obj_tag(v_e_701_))
{
case 3:
{
lean_object* v_us_703_; lean_object* v_args_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_us_703_ = lean_ctor_get(v_e_701_, 1);
lean_inc(v_us_703_);
v_args_704_ = lean_ctor_get(v_e_701_, 2);
lean_inc_ref(v_args_704_);
lean_dec_ref(v_e_701_);
v___x_705_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_704_, v_a_702_);
lean_dec_ref(v_args_704_);
v___x_706_ = l_Lean_CollectLevelParams_visitLevels(v_us_703_, v___x_705_);
return v___x_706_;
}
case 4:
{
lean_object* v_args_707_; lean_object* v___x_708_; 
v_args_707_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_args_707_);
lean_dec_ref(v_e_701_);
v___x_708_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_707_, v_a_702_);
lean_dec_ref(v_args_707_);
return v___x_708_;
}
default: 
{
lean_dec(v_e_701_);
return v_a_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_type_711_; lean_object* v___x_712_; 
v_type_711_ = lean_ctor_get(v_p_709_, 2);
lean_inc_ref(v_type_711_);
lean_dec_ref(v_p_709_);
v___x_712_ = l_Lean_CollectLevelParams_visitExpr(v_type_711_, v_a_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_713_, size_t v_i_714_, size_t v_stop_715_, lean_object* v_b_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_eq(v_i_714_, v_stop_715_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; size_t v___x_720_; size_t v___x_721_; 
v___x_718_ = lean_array_uget_borrowed(v_as_713_, v_i_714_);
lean_inc(v___x_718_);
v___x_719_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_718_, v_b_716_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_714_, v___x_720_);
v_i_714_ = v___x_721_;
v_b_716_ = v___x_719_;
goto _start;
}
else
{
return v_b_716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_723_, lean_object* v_i_724_, lean_object* v_stop_725_, lean_object* v_b_726_){
_start:
{
size_t v_i_boxed_727_; size_t v_stop_boxed_728_; lean_object* v_res_729_; 
v_i_boxed_727_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_stop_boxed_728_ = lean_unbox_usize(v_stop_725_);
lean_dec(v_stop_725_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_723_, v_i_boxed_727_, v_stop_boxed_728_, v_b_726_);
lean_dec_ref(v_as_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_730_, lean_object* v_s_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_ps_730_);
v___x_734_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
return v_s_731_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_733_);
if (v___x_735_ == 0)
{
if (v___x_734_ == 0)
{
return v_s_731_;
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_733_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_730_, v___x_736_, v___x_737_, v_s_731_);
return v___x_738_;
}
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_733_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_730_, v___x_739_, v___x_740_, v_s_731_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_742_, lean_object* v_s_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_742_, v_s_743_);
lean_dec_ref(v_ps_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_745_, size_t v_i_746_, size_t v_stop_747_, lean_object* v_b_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_eq(v_i_746_, v_stop_747_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; size_t v___x_752_; size_t v___x_753_; 
v___x_750_ = lean_array_uget_borrowed(v_as_745_, v_i_746_);
lean_inc(v___x_750_);
v___x_751_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_750_, v_b_748_);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_746_, v___x_752_);
v_i_746_ = v___x_753_;
v_b_748_ = v___x_751_;
goto _start;
}
else
{
return v_b_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_755_, lean_object* v_s_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_array_get_size(v_alts_755_);
v___x_759_ = lean_nat_dec_lt(v___x_757_, v___x_758_);
if (v___x_759_ == 0)
{
return v_s_756_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v___x_758_, v___x_758_);
if (v___x_760_ == 0)
{
if (v___x_759_ == 0)
{
return v_s_756_;
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_758_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_755_, v___x_761_, v___x_762_, v_s_756_);
return v___x_763_;
}
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_758_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_755_, v___x_764_, v___x_765_, v_s_756_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_767_, lean_object* v_a_768_){
_start:
{
switch(lean_obj_tag(v_x_767_))
{
case 0:
{
lean_object* v_decl_769_; lean_object* v_k_770_; lean_object* v_type_771_; lean_object* v_value_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_decl_769_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_decl_769_);
v_k_770_ = lean_ctor_get(v_x_767_, 1);
lean_inc_ref(v_k_770_);
lean_dec_ref(v_x_767_);
v_type_771_ = lean_ctor_get(v_decl_769_, 2);
lean_inc_ref(v_type_771_);
v_value_772_ = lean_ctor_get(v_decl_769_, 3);
lean_inc(v_value_772_);
lean_dec_ref(v_decl_769_);
v___x_773_ = l_Lean_CollectLevelParams_visitExpr(v_type_771_, v_a_768_);
v___x_774_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_772_, v___x_773_);
v_x_767_ = v_k_770_;
v_a_768_ = v___x_774_;
goto _start;
}
case 3:
{
lean_object* v_args_776_; lean_object* v___x_777_; 
v_args_776_ = lean_ctor_get(v_x_767_, 1);
lean_inc_ref(v_args_776_);
lean_dec_ref(v_x_767_);
v___x_777_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_776_, v_a_768_);
lean_dec_ref(v_args_776_);
return v___x_777_;
}
case 4:
{
lean_object* v_cases_778_; lean_object* v_resultType_779_; lean_object* v_alts_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_cases_778_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_cases_778_);
lean_dec_ref(v_x_767_);
v_resultType_779_ = lean_ctor_get(v_cases_778_, 1);
lean_inc_ref(v_resultType_779_);
v_alts_780_ = lean_ctor_get(v_cases_778_, 3);
lean_inc_ref(v_alts_780_);
lean_dec_ref(v_cases_778_);
v___x_781_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_779_, v_a_768_);
v___x_782_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_780_, v___x_781_);
lean_dec_ref(v_alts_780_);
return v___x_782_;
}
case 5:
{
lean_dec_ref(v_x_767_);
return v_a_768_;
}
case 6:
{
lean_object* v_type_783_; lean_object* v___x_784_; 
v_type_783_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_type_783_);
lean_dec_ref(v_x_767_);
v___x_784_ = l_Lean_CollectLevelParams_visitExpr(v_type_783_, v_a_768_);
return v___x_784_;
}
default: 
{
lean_object* v_decl_785_; lean_object* v_k_786_; lean_object* v_params_787_; lean_object* v_type_788_; lean_object* v_value_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_decl_785_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_decl_785_);
v_k_786_ = lean_ctor_get(v_x_767_, 1);
lean_inc_ref(v_k_786_);
lean_dec_ref(v_x_767_);
v_params_787_ = lean_ctor_get(v_decl_785_, 2);
lean_inc_ref(v_params_787_);
v_type_788_ = lean_ctor_get(v_decl_785_, 3);
lean_inc_ref(v_type_788_);
v_value_789_ = lean_ctor_get(v_decl_785_, 4);
lean_inc_ref(v_value_789_);
lean_dec_ref(v_decl_785_);
v___x_790_ = l_Lean_CollectLevelParams_visitExpr(v_type_788_, v_a_768_);
v___x_791_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_787_, v___x_790_);
lean_dec_ref(v_params_787_);
v___x_792_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_789_, v___x_791_);
v_x_767_ = v_k_786_;
v_a_768_ = v___x_792_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_794_, lean_object* v_a_795_){
_start:
{
if (lean_obj_tag(v_alt_794_) == 0)
{
lean_object* v_params_796_; lean_object* v_code_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_params_796_ = lean_ctor_get(v_alt_794_, 1);
lean_inc_ref(v_params_796_);
v_code_797_ = lean_ctor_get(v_alt_794_, 2);
lean_inc_ref(v_code_797_);
lean_dec_ref(v_alt_794_);
v___x_798_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_796_, v_a_795_);
lean_dec_ref(v_params_796_);
v___x_799_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_797_, v___x_798_);
return v___x_799_;
}
else
{
lean_object* v_code_800_; lean_object* v___x_801_; 
v_code_800_ = lean_ctor_get(v_alt_794_, 0);
lean_inc_ref(v_code_800_);
lean_dec_ref(v_alt_794_);
v___x_801_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_800_, v_a_795_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_802_, lean_object* v_i_803_, lean_object* v_stop_804_, lean_object* v_b_805_){
_start:
{
size_t v_i_boxed_806_; size_t v_stop_boxed_807_; lean_object* v_res_808_; 
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_stop_boxed_807_ = lean_unbox_usize(v_stop_804_);
lean_dec(v_stop_804_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_802_, v_i_boxed_806_, v_stop_boxed_807_, v_b_805_);
lean_dec_ref(v_as_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_809_, lean_object* v_s_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_809_, v_s_810_);
lean_dec_ref(v_alts_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_812_, lean_object* v_a_813_){
_start:
{
if (lean_obj_tag(v_x_812_) == 0)
{
lean_object* v_code_814_; lean_object* v___x_815_; 
v_code_814_ = lean_ctor_get(v_x_812_, 0);
lean_inc_ref(v_code_814_);
lean_dec_ref(v_x_812_);
v___x_815_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_814_, v_a_813_);
return v___x_815_;
}
else
{
lean_dec_ref(v_x_812_);
return v_a_813_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_unsigned_to_nat(16u);
v___x_818_ = lean_mk_array(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_823_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
lean_ctor_set(v___x_824_, 2, v___x_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_825_){
_start:
{
lean_object* v_toSignature_826_; lean_object* v_value_827_; uint8_t v_recursive_828_; lean_object* v_inlineAttr_x3f_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_854_; 
v_toSignature_826_ = lean_ctor_get(v_decl_825_, 0);
v_value_827_ = lean_ctor_get(v_decl_825_, 1);
v_recursive_828_ = lean_ctor_get_uint8(v_decl_825_, sizeof(void*)*3);
v_inlineAttr_x3f_829_ = lean_ctor_get(v_decl_825_, 2);
v_isSharedCheck_854_ = !lean_is_exclusive(v_decl_825_);
if (v_isSharedCheck_854_ == 0)
{
v___x_831_ = v_decl_825_;
v_isShared_832_ = v_isSharedCheck_854_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_inlineAttr_x3f_829_);
lean_inc(v_value_827_);
lean_inc(v_toSignature_826_);
lean_dec(v_decl_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_854_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_name_833_; lean_object* v_type_834_; lean_object* v_params_835_; uint8_t v_safe_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_852_; 
v_name_833_ = lean_ctor_get(v_toSignature_826_, 0);
v_type_834_ = lean_ctor_get(v_toSignature_826_, 2);
v_params_835_ = lean_ctor_get(v_toSignature_826_, 3);
v_safe_836_ = lean_ctor_get_uint8(v_toSignature_826_, sizeof(void*)*4);
v_isSharedCheck_852_ = !lean_is_exclusive(v_toSignature_826_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_toSignature_826_, 1);
lean_dec(v_unused_853_);
v___x_838_ = v_toSignature_826_;
v_isShared_839_ = v_isSharedCheck_852_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_params_835_);
lean_inc(v_type_834_);
lean_inc(v_name_833_);
lean_dec(v_toSignature_826_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_852_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_params_844_; lean_object* v_levelParams_845_; lean_object* v___x_847_; 
v___x_840_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_834_);
v___x_841_ = l_Lean_CollectLevelParams_visitExpr(v_type_834_, v___x_840_);
v___x_842_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_835_, v___x_841_);
lean_inc_ref(v_value_827_);
v___x_843_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_827_, v___x_842_);
v_params_844_ = lean_ctor_get(v___x_843_, 2);
lean_inc_ref(v_params_844_);
lean_dec_ref(v___x_843_);
v_levelParams_845_ = lean_array_to_list(v_params_844_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_levelParams_845_);
v___x_847_ = v___x_838_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_name_833_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_levelParams_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_type_834_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_params_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_851_, sizeof(void*)*4, v_safe_836_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_847_);
v___x_849_ = v___x_831_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_value_827_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_inlineAttr_x3f_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_850_, sizeof(void*)*3, v_recursive_828_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
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
