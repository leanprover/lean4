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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_nbuckets_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_96_ = lean_array_get_size(v_data_95_);
v___x_97_ = lean_unsigned_to_nat(2u);
v_nbuckets_98_ = lean_nat_mul(v___x_96_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_box(0);
v___x_101_ = lean_mk_array(v_nbuckets_98_, v___x_100_);
v___x_102_ = lean_array_propagate_mark(v_data_95_, v___x_101_);
v___x_103_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v___x_99_, v_data_95_, v___x_102_);
return v___x_103_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object* v_a_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
else
{
lean_object* v_key_107_; lean_object* v_tail_108_; uint8_t v___x_109_; 
v_key_107_ = lean_ctor_get(v_x_105_, 0);
v_tail_108_ = lean_ctor_get(v_x_105_, 2);
v___x_109_ = lean_name_eq(v_key_107_, v_a_104_);
if (v___x_109_ == 0)
{
v_x_105_ = v_tail_108_;
goto _start;
}
else
{
return v___x_109_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_104_ = stack[0].m_obj;
lean_object* v_x_105_ = stack[1].m_obj;
uint8_t v_res_111_;
v_res_111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_104_, v_x_105_);
stack->m_num = v_res_111_;
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
v___x_164_ = 1723ULL;
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
v___x_198_ = 1723ULL;
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
lean_object* v_a_238_; lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v___x_243_; lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_267_; 
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
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_267_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_267_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_snd_245_);
lean_inc(v_fst_244_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_267_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_ptr_addr(v_a_238_);
v___x_250_ = lean_ptr_addr(v_fst_241_);
v___x_251_ = lean_usize_dec_eq(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_252_ = l_Lean_mkLevelMax_x27(v_fst_241_, v_fst_244_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_252_);
v___x_254_ = v___x_247_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_snd_245_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
size_t v___x_256_; size_t v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_ptr_addr(v_a_239_);
v___x_257_ = lean_ptr_addr(v_fst_244_);
v___x_258_ = lean_usize_dec_eq(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_259_ = l_Lean_mkLevelMax_x27(v_fst_241_, v_fst_244_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_259_);
v___x_261_ = v___x_247_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_snd_245_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = l_Lean_simpLevelMax_x27(v_fst_241_, v_fst_244_, v_u_215_);
lean_dec_ref_known(v_u_215_, 2);
lean_dec(v_fst_244_);
lean_dec(v_fst_241_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_263_);
v___x_265_ = v___x_247_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_snd_245_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
case 3:
{
lean_object* v_a_268_; lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_297_; 
v_a_268_ = lean_ctor_get(v_u_215_, 0);
v_a_269_ = lean_ctor_get(v_u_215_, 1);
lean_inc(v_a_268_);
v___x_270_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_268_, v_a_216_);
v_fst_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_fst_271_);
v_snd_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_snd_272_);
lean_dec_ref(v___x_270_);
lean_inc(v_a_269_);
v___x_273_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_269_, v_snd_272_);
v_fst_274_ = lean_ctor_get(v___x_273_, 0);
v_snd_275_ = lean_ctor_get(v___x_273_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_297_ == 0)
{
v___x_277_ = v___x_273_;
v_isShared_278_ = v_isSharedCheck_297_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_snd_275_);
lean_inc(v_fst_274_);
lean_dec(v___x_273_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_297_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
size_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_ptr_addr(v_a_268_);
v___x_280_ = lean_ptr_addr(v_fst_271_);
v___x_281_ = lean_usize_dec_eq(v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_282_ = l_Lean_mkLevelIMax_x27(v_fst_271_, v_fst_274_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_282_);
v___x_284_ = v___x_277_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_275_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
else
{
size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_ptr_addr(v_a_269_);
v___x_287_ = lean_ptr_addr(v_fst_274_);
v___x_288_ = lean_usize_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec_ref_known(v_u_215_, 2);
v___x_289_ = l_Lean_mkLevelIMax_x27(v_fst_271_, v_fst_274_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_289_);
v___x_291_ = v___x_277_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_275_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_simpLevelIMax_x27(v_fst_271_, v_fst_274_, v_u_215_);
lean_dec_ref_known(v_u_215_, 2);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_293_);
v___x_295_ = v___x_277_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_snd_275_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
case 4:
{
lean_object* v_a_298_; lean_object* v_nextIdx_299_; lean_object* v_map_300_; lean_object* v_paramNames_301_; lean_object* v___x_302_; 
v_a_298_ = lean_ctor_get(v_u_215_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v_u_215_, 1);
v_nextIdx_299_ = lean_ctor_get(v_a_216_, 0);
v_map_300_ = lean_ctor_get(v_a_216_, 1);
v_paramNames_301_ = lean_ctor_get(v_a_216_, 2);
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_300_, v_a_298_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_paramNames_301_);
lean_inc_ref(v_map_300_);
lean_inc(v_nextIdx_299_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; 
v_unused_318_ = lean_ctor_get(v_a_216_, 2);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_a_216_, 1);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_a_216_, 0);
lean_dec(v_unused_320_);
v___x_304_ = v_a_216_;
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_a_216_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_317_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_306_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_299_);
v___x_307_ = lean_name_append_index_after(v___x_306_, v_nextIdx_299_);
v___x_308_ = l_Lean_Level_param___override(v___x_307_);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_nextIdx_299_, v___x_309_);
lean_dec(v_nextIdx_299_);
lean_inc(v___x_308_);
lean_inc(v_a_298_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_300_, v_a_298_, v___x_308_);
v___x_312_ = lean_array_push(v_paramNames_301_, v_a_298_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_312_);
lean_ctor_set(v___x_304_, 1, v___x_311_);
lean_ctor_set(v___x_304_, 0, v___x_310_);
v___x_314_ = v___x_304_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v___x_312_);
v___x_314_ = v_reuseFailAlloc_316_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_308_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
return v___x_315_;
}
}
}
else
{
lean_object* v_val_321_; lean_object* v___x_322_; 
lean_dec(v_a_298_);
v_val_321_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_302_, 1);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_val_321_);
lean_ctor_set(v___x_322_, 1, v_a_216_);
return v___x_322_;
}
}
default: 
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec_ref_known(v_u_215_, 1);
v___x_323_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_324_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_323_, v_a_216_);
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_325_, lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_326_, v_a_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_329_, lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_329_, v_m_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_m_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_333_, lean_object* v_m_334_, lean_object* v_a_335_, lean_object* v_b_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_334_, v_a_335_, v_b_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_338_, lean_object* v_a_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_342_, lean_object* v_a_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_342_, v_a_343_, v_x_344_);
lean_dec(v_x_344_);
lean_dec(v_a_343_);
return v_res_345_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_346_, lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_347_ = stack[1].m_obj;
lean_object* v_x_348_ = stack[2].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_box(0), v_a_347_, v_x_348_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_351_, lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_351_, v_a_352_, v_x_353_);
lean_dec(v_x_353_);
lean_dec(v_a_352_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_356_, lean_object* v_data_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_359_, lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_360_, v_b_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_364_, lean_object* v_i_365_, lean_object* v_source_366_, lean_object* v_target_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_365_, v_source_366_, v_target_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_369_, lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_4908__overap_397_; lean_object* v___x_398_; 
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_380_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_381_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___f_375_);
lean_ctor_set(v___x_382_, 1, v___f_376_);
v___x_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___f_377_);
lean_ctor_set(v___x_383_, 2, v___f_378_);
lean_ctor_set(v___x_383_, 3, v___f_379_);
lean_ctor_set(v___x_383_, 4, v___f_380_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___f_381_);
lean_inc_ref_n(v___x_384_, 6);
v___f_385_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_385_, 0, v___x_384_);
v___f_386_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_386_, 0, v___x_384_);
v___f_387_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_387_, 0, v___x_384_);
v___f_388_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_388_, 0, v___x_384_);
v___x_389_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, lean_box(0));
lean_closure_set(v___x_389_, 2, v___x_384_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___f_385_);
v___x_391_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, lean_box(0));
lean_closure_set(v___x_391_, 2, v___x_384_);
v___x_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
lean_ctor_set(v___x_392_, 2, v___f_386_);
lean_ctor_set(v___x_392_, 3, v___f_387_);
lean_ctor_set(v___x_392_, 4, v___f_388_);
v___x_393_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_393_, 0, lean_box(0));
lean_closure_set(v___x_393_, 1, lean_box(0));
lean_closure_set(v___x_393_, 2, v___x_384_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_instInhabitedExpr;
v___x_396_ = l_instInhabitedOfMonad___redArg(v___x_394_, v___x_395_);
v___x_4908__overap_397_ = lean_panic_fn_borrowed(v___x_396_, v_msg_373_);
lean_dec(v___x_396_);
v___x_398_ = lean_apply_1(v___x_4908__overap_397_, v___y_374_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v___y_401_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = l_List_reverse___redArg(v_x_400_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___y_401_);
return v___x_403_;
}
else
{
lean_object* v_head_404_; lean_object* v_tail_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_416_; 
v_head_404_ = lean_ctor_get(v_x_399_, 0);
v_tail_405_ = lean_ctor_get(v_x_399_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_407_ = v_x_399_;
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_tail_405_);
lean_inc(v_head_404_);
lean_dec(v_x_399_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_416_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; 
v___x_409_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_404_, v___y_401_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 1, v_x_400_);
lean_ctor_set(v___x_407_, 0, v_fst_410_);
v___x_413_ = v___x_407_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_fst_410_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_x_400_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
v_x_399_ = v_tail_405_;
v_x_400_ = v___x_413_;
v___y_401_ = v_snd_411_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_419_ = lean_unsigned_to_nat(26u);
v___x_420_ = lean_unsigned_to_nat(79u);
v___x_421_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_422_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_423_ = l_mkPanicMessageWithDecl(v___x_422_, v___x_421_, v___x_420_, v___x_419_, v___x_418_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_424_, lean_object* v_a_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = l_Lean_Expr_hasLevelParam(v_e_424_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_e_424_);
lean_ctor_set(v___x_427_, 1, v_a_425_);
return v___x_427_;
}
else
{
switch(lean_obj_tag(v_e_424_))
{
case 4:
{
lean_object* v_declName_428_; lean_object* v_us_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_445_; 
v_declName_428_ = lean_ctor_get(v_e_424_, 0);
v_us_429_ = lean_ctor_get(v_e_424_, 1);
v___x_430_ = lean_box(0);
lean_inc(v_us_429_);
v___x_431_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_429_, v___x_430_, v_a_425_);
v_fst_432_ = lean_ctor_get(v___x_431_, 0);
v_snd_433_ = lean_ctor_get(v___x_431_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_445_ == 0)
{
v___x_435_ = v___x_431_;
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_433_);
lean_inc(v_fst_432_);
lean_dec(v___x_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
uint8_t v___x_437_; 
v___x_437_ = l_ptrEqList___redArg(v_us_429_, v_fst_432_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_inc(v_declName_428_);
lean_dec_ref_known(v_e_424_, 2);
v___x_438_ = l_Lean_Expr_const___override(v_declName_428_, v_fst_432_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_snd_433_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v_fst_432_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_e_424_);
v___x_443_ = v___x_435_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_snd_433_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
case 3:
{
lean_object* v_u_446_; lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_463_; 
v_u_446_ = lean_ctor_get(v_e_424_, 0);
lean_inc(v_u_446_);
v___x_447_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_446_, v_a_425_);
v_fst_448_ = lean_ctor_get(v___x_447_, 0);
v_snd_449_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_463_ == 0)
{
v___x_451_ = v___x_447_;
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v___x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_463_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_ptr_addr(v_u_446_);
v___x_454_ = lean_ptr_addr(v_fst_448_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec_ref_known(v_e_424_, 1);
v___x_456_ = l_Lean_Expr_sort___override(v_fst_448_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_456_);
v___x_458_ = v___x_451_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_snd_449_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_461_; 
lean_dec(v_fst_448_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_e_424_);
v___x_461_ = v___x_451_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_snd_449_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
case 5:
{
lean_object* v_fn_464_; lean_object* v_arg_465_; lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_492_; 
v_fn_464_ = lean_ctor_get(v_e_424_, 0);
v_arg_465_ = lean_ctor_get(v_e_424_, 1);
lean_inc_ref(v_fn_464_);
v___x_466_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_464_, v_a_425_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_466_);
lean_inc_ref(v_arg_465_);
v___x_469_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_465_, v_snd_468_);
v_fst_470_ = lean_ctor_get(v___x_469_, 0);
v_snd_471_ = lean_ctor_get(v___x_469_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_492_ == 0)
{
v___x_473_ = v___x_469_;
v_isShared_474_ = v_isSharedCheck_492_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_inc(v_fst_470_);
lean_dec(v___x_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_492_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
size_t v___x_475_; size_t v___x_476_; uint8_t v___x_477_; 
v___x_475_ = lean_ptr_addr(v_fn_464_);
v___x_476_ = lean_ptr_addr(v_fst_467_);
v___x_477_ = lean_usize_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec_ref_known(v_e_424_, 2);
v___x_478_ = l_Lean_Expr_app___override(v_fst_467_, v_fst_470_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_478_);
v___x_480_ = v___x_473_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_snd_471_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_ptr_addr(v_arg_465_);
v___x_483_ = lean_ptr_addr(v_fst_470_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec_ref_known(v_e_424_, 2);
v___x_485_ = l_Lean_Expr_app___override(v_fst_467_, v_fst_470_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_485_);
v___x_487_ = v___x_473_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_471_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec(v_fst_470_);
lean_dec(v_fst_467_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v_e_424_);
v___x_490_ = v___x_473_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_snd_471_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_493_; lean_object* v_type_494_; lean_object* v_value_495_; lean_object* v_body_496_; uint8_t v_nondep_497_; lean_object* v___x_498_; lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_534_; 
v_declName_493_ = lean_ctor_get(v_e_424_, 0);
v_type_494_ = lean_ctor_get(v_e_424_, 1);
v_value_495_ = lean_ctor_get(v_e_424_, 2);
v_body_496_ = lean_ctor_get(v_e_424_, 3);
v_nondep_497_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_494_);
v___x_498_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_494_, v_a_425_);
v_fst_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_fst_499_);
v_snd_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_snd_500_);
lean_dec_ref(v___x_498_);
lean_inc_ref(v_value_495_);
v___x_501_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_495_, v_snd_500_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_fst_502_);
v_snd_503_ = lean_ctor_get(v___x_501_, 1);
lean_inc(v_snd_503_);
lean_dec_ref(v___x_501_);
lean_inc_ref(v_body_496_);
v___x_504_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_496_, v_snd_503_);
v_fst_505_ = lean_ctor_get(v___x_504_, 0);
v_snd_506_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_534_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_534_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_534_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_ptr_addr(v_type_494_);
v___x_511_ = lean_ptr_addr(v_fst_499_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_inc(v_declName_493_);
lean_dec_ref_known(v_e_424_, 4);
v___x_513_ = l_Lean_Expr_letE___override(v_declName_493_, v_fst_499_, v_fst_502_, v_fst_505_, v_nondep_497_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_513_);
v___x_515_ = v___x_508_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_snd_506_);
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
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = lean_ptr_addr(v_value_495_);
v___x_518_ = lean_ptr_addr(v_fst_502_);
v___x_519_ = lean_usize_dec_eq(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_inc(v_declName_493_);
lean_dec_ref_known(v_e_424_, 4);
v___x_520_ = l_Lean_Expr_letE___override(v_declName_493_, v_fst_499_, v_fst_502_, v_fst_505_, v_nondep_497_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_520_);
v___x_522_ = v___x_508_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_snd_506_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_ptr_addr(v_body_496_);
v___x_525_ = lean_ptr_addr(v_fst_505_);
v___x_526_ = lean_usize_dec_eq(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_inc(v_declName_493_);
lean_dec_ref_known(v_e_424_, 4);
v___x_527_ = l_Lean_Expr_letE___override(v_declName_493_, v_fst_499_, v_fst_502_, v_fst_505_, v_nondep_497_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_527_);
v___x_529_ = v___x_508_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_506_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v___x_532_; 
lean_dec(v_fst_505_);
lean_dec(v_fst_502_);
lean_dec(v_fst_499_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_e_424_);
v___x_532_ = v___x_508_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_snd_506_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_535_; lean_object* v_binderType_536_; lean_object* v_body_537_; uint8_t v_binderInfo_538_; lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_542_; lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_570_; 
v_binderName_535_ = lean_ctor_get(v_e_424_, 0);
v_binderType_536_ = lean_ctor_get(v_e_424_, 1);
v_body_537_ = lean_ctor_get(v_e_424_, 2);
v_binderInfo_538_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_536_);
v___x_539_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_536_, v_a_425_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v___x_539_);
lean_inc_ref(v_body_537_);
v___x_542_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_537_, v_snd_541_);
v_fst_543_ = lean_ctor_get(v___x_542_, 0);
v_snd_544_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_570_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_570_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_543_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_570_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_ptr_addr(v_binderType_536_);
v___x_549_ = lean_ptr_addr(v_fst_540_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_binderName_535_);
lean_dec_ref_known(v_e_424_, 3);
v___x_551_ = l_Lean_Expr_forallE___override(v_binderName_535_, v_fst_540_, v_fst_543_, v_binderInfo_538_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_551_);
v___x_553_ = v___x_546_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_snd_544_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_ptr_addr(v_body_537_);
v___x_556_ = lean_ptr_addr(v_fst_543_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_inc(v_binderName_535_);
lean_dec_ref_known(v_e_424_, 3);
v___x_558_ = l_Lean_Expr_forallE___override(v_binderName_535_, v_fst_540_, v_fst_543_, v_binderInfo_538_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_558_);
v___x_560_ = v___x_546_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_544_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
uint8_t v___x_562_; 
v___x_562_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_538_, v_binderInfo_538_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_inc(v_binderName_535_);
lean_dec_ref_known(v_e_424_, 3);
v___x_563_ = l_Lean_Expr_forallE___override(v_binderName_535_, v_fst_540_, v_fst_543_, v_binderInfo_538_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_563_);
v___x_565_ = v___x_546_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_544_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v_fst_543_);
lean_dec(v_fst_540_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_e_424_);
v___x_568_ = v___x_546_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_544_);
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
case 6:
{
lean_object* v_binderName_571_; lean_object* v_binderType_572_; lean_object* v_body_573_; uint8_t v_binderInfo_574_; lean_object* v___x_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_606_; 
v_binderName_571_ = lean_ctor_get(v_e_424_, 0);
v_binderType_572_ = lean_ctor_get(v_e_424_, 1);
v_body_573_ = lean_ctor_get(v_e_424_, 2);
v_binderInfo_574_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_572_);
v___x_575_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_572_, v_a_425_);
v_fst_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_snd_577_);
lean_dec_ref(v___x_575_);
lean_inc_ref(v_body_573_);
v___x_578_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_573_, v_snd_577_);
v_fst_579_ = lean_ctor_get(v___x_578_, 0);
v_snd_580_ = lean_ctor_get(v___x_578_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_606_ == 0)
{
v___x_582_ = v___x_578_;
v_isShared_583_ = v_isSharedCheck_606_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snd_580_);
lean_inc(v_fst_579_);
lean_dec(v___x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_606_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
size_t v___x_584_; size_t v___x_585_; uint8_t v___x_586_; 
v___x_584_ = lean_ptr_addr(v_binderType_572_);
v___x_585_ = lean_ptr_addr(v_fst_576_);
v___x_586_ = lean_usize_dec_eq(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_inc(v_binderName_571_);
lean_dec_ref_known(v_e_424_, 3);
v___x_587_ = l_Lean_Expr_lam___override(v_binderName_571_, v_fst_576_, v_fst_579_, v_binderInfo_574_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_587_);
v___x_589_ = v___x_582_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_snd_580_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
size_t v___x_591_; size_t v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_ptr_addr(v_body_573_);
v___x_592_ = lean_ptr_addr(v_fst_579_);
v___x_593_ = lean_usize_dec_eq(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
lean_inc(v_binderName_571_);
lean_dec_ref_known(v_e_424_, 3);
v___x_594_ = l_Lean_Expr_lam___override(v_binderName_571_, v_fst_576_, v_fst_579_, v_binderInfo_574_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_594_);
v___x_596_ = v___x_582_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_snd_580_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
else
{
uint8_t v___x_598_; 
v___x_598_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_574_, v_binderInfo_574_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_601_; 
lean_inc(v_binderName_571_);
lean_dec_ref_known(v_e_424_, 3);
v___x_599_ = l_Lean_Expr_lam___override(v_binderName_571_, v_fst_576_, v_fst_579_, v_binderInfo_574_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_599_);
v___x_601_ = v___x_582_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_snd_580_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
lean_object* v___x_604_; 
lean_dec(v_fst_579_);
lean_dec(v_fst_576_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_e_424_);
v___x_604_ = v___x_582_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_580_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_607_; lean_object* v_expr_608_; lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_625_; 
v_data_607_ = lean_ctor_get(v_e_424_, 0);
v_expr_608_ = lean_ctor_get(v_e_424_, 1);
lean_inc_ref(v_expr_608_);
v___x_609_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_608_, v_a_425_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_625_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
size_t v___x_615_; size_t v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_ptr_addr(v_expr_608_);
v___x_616_ = lean_ptr_addr(v_fst_610_);
v___x_617_ = lean_usize_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_620_; 
lean_inc(v_data_607_);
lean_dec_ref_known(v_e_424_, 2);
v___x_618_ = l_Lean_Expr_mdata___override(v_data_607_, v_fst_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_618_);
v___x_620_ = v___x_613_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_snd_611_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_fst_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_e_424_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_snd_611_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
case 11:
{
lean_object* v_typeName_626_; lean_object* v_idx_627_; lean_object* v_struct_628_; lean_object* v___x_629_; lean_object* v_fst_630_; lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_645_; 
v_typeName_626_ = lean_ctor_get(v_e_424_, 0);
v_idx_627_ = lean_ctor_get(v_e_424_, 1);
v_struct_628_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_struct_628_);
v___x_629_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_628_, v_a_425_);
v_fst_630_ = lean_ctor_get(v___x_629_, 0);
v_snd_631_ = lean_ctor_get(v___x_629_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_645_ == 0)
{
v___x_633_ = v___x_629_;
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_inc(v_fst_630_);
lean_dec(v___x_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_645_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
size_t v___x_635_; size_t v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_ptr_addr(v_struct_628_);
v___x_636_ = lean_ptr_addr(v_fst_630_);
v___x_637_ = lean_usize_dec_eq(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_640_; 
lean_inc(v_idx_627_);
lean_inc(v_typeName_626_);
lean_dec_ref_known(v_e_424_, 3);
v___x_638_ = l_Lean_Expr_proj___override(v_typeName_626_, v_idx_627_, v_fst_630_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_638_);
v___x_640_ = v___x_633_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_snd_631_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_fst_630_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v_e_424_);
v___x_643_ = v___x_633_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_e_424_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_snd_631_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
case 2:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref_known(v_e_424_, 1);
v___x_646_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_647_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_646_, v_a_425_);
return v___x_647_;
}
default: 
{
lean_object* v___x_648_; 
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_e_424_);
lean_ctor_set(v___x_648_, 1, v_a_425_);
return v___x_648_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_box(0);
v___x_650_ = lean_unsigned_to_nat(16u);
v___x_651_ = lean_mk_array(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_658_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
lean_ctor_set(v___x_660_, 2, v___x_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_snd_664_; lean_object* v_fst_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_674_; 
v___x_662_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_663_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_661_, v___x_662_);
v_snd_664_ = lean_ctor_get(v___x_663_, 1);
v_fst_665_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_674_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_snd_664_);
lean_inc(v_fst_665_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_674_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_paramNames_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v_paramNames_669_ = lean_ctor_get(v_snd_664_, 2);
lean_inc_ref(v_paramNames_669_);
lean_dec(v_snd_664_);
v___x_670_ = lean_array_to_list(v_paramNames_669_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_fst_665_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_CollectLevelParams_visitExpr(v_type_675_, v_a_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_678_, lean_object* v_a_679_){
_start:
{
if (lean_obj_tag(v_arg_678_) == 2)
{
lean_object* v_expr_680_; lean_object* v___x_681_; 
v_expr_680_ = lean_ctor_get(v_arg_678_, 0);
lean_inc_ref(v_expr_680_);
lean_dec_ref_known(v_arg_678_, 1);
v___x_681_ = l_Lean_CollectLevelParams_visitExpr(v_expr_680_, v_a_679_);
return v___x_681_;
}
else
{
lean_dec(v_arg_678_);
return v_a_679_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_682_, size_t v_i_683_, size_t v_stop_684_, lean_object* v_b_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_eq(v_i_683_, v_stop_684_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; size_t v___x_689_; size_t v___x_690_; 
v___x_687_ = lean_array_uget_borrowed(v_as_682_, v_i_683_);
lean_inc(v___x_687_);
v___x_688_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_687_, v_b_685_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_683_, v___x_689_);
v_i_683_ = v___x_690_;
v_b_685_ = v___x_688_;
goto _start;
}
else
{
return v_b_685_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_682_ = stack[0].m_obj;
size_t v_i_683_ = stack[1].m_num;
size_t v_stop_684_ = stack[2].m_num;
lean_object* v_b_685_ = stack[3].m_obj;
lean_object* v_res_692_;
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_682_, v_i_683_, v_stop_684_, v_b_685_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_693_, lean_object* v_i_694_, lean_object* v_stop_695_, lean_object* v_b_696_){
_start:
{
size_t v_i_boxed_697_; size_t v_stop_boxed_698_; lean_object* v_res_699_; 
v_i_boxed_697_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_stop_boxed_698_ = lean_unbox_usize(v_stop_695_);
lean_dec(v_stop_695_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_693_, v_i_boxed_697_, v_stop_boxed_698_, v_b_696_);
lean_dec_ref(v_as_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_700_, lean_object* v_s_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_array_get_size(v_args_700_);
v___x_704_ = lean_nat_dec_lt(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
return v_s_701_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_le(v___x_703_, v___x_703_);
if (v___x_705_ == 0)
{
if (v___x_704_ == 0)
{
return v_s_701_;
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_703_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_700_, v___x_706_, v___x_707_, v_s_701_);
return v___x_708_;
}
}
else
{
size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_703_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_700_, v___x_709_, v___x_710_, v_s_701_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_712_, lean_object* v_s_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_712_, v_s_713_);
lean_dec_ref(v_args_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_715_, lean_object* v_a_716_){
_start:
{
switch(lean_obj_tag(v_e_715_))
{
case 3:
{
lean_object* v_us_717_; lean_object* v_args_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_us_717_ = lean_ctor_get(v_e_715_, 1);
lean_inc(v_us_717_);
v_args_718_ = lean_ctor_get(v_e_715_, 2);
lean_inc_ref(v_args_718_);
lean_dec_ref_known(v_e_715_, 3);
v___x_719_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_718_, v_a_716_);
lean_dec_ref(v_args_718_);
v___x_720_ = l_Lean_CollectLevelParams_visitLevels(v_us_717_, v___x_719_);
return v___x_720_;
}
case 4:
{
lean_object* v_args_721_; lean_object* v___x_722_; 
v_args_721_ = lean_ctor_get(v_e_715_, 1);
lean_inc_ref(v_args_721_);
lean_dec_ref_known(v_e_715_, 2);
v___x_722_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_721_, v_a_716_);
lean_dec_ref(v_args_721_);
return v___x_722_;
}
default: 
{
lean_dec(v_e_715_);
return v_a_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_type_725_; lean_object* v___x_726_; 
v_type_725_ = lean_ctor_get(v_p_723_, 2);
lean_inc_ref(v_type_725_);
lean_dec_ref(v_p_723_);
v___x_726_ = l_Lean_CollectLevelParams_visitExpr(v_type_725_, v_a_724_);
return v___x_726_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_727_, size_t v_i_728_, size_t v_stop_729_, lean_object* v_b_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_eq(v_i_728_, v_stop_729_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; 
v___x_732_ = lean_array_uget_borrowed(v_as_727_, v_i_728_);
lean_inc(v___x_732_);
v___x_733_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_732_, v_b_730_);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_728_, v___x_734_);
v_i_728_ = v___x_735_;
v_b_730_ = v___x_733_;
goto _start;
}
else
{
return v_b_730_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_727_ = stack[0].m_obj;
size_t v_i_728_ = stack[1].m_num;
size_t v_stop_729_ = stack[2].m_num;
lean_object* v_b_730_ = stack[3].m_obj;
lean_object* v_res_737_;
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_727_, v_i_728_, v_stop_729_, v_b_730_);
stack->m_obj
 = v_res_737_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_738_, lean_object* v_i_739_, lean_object* v_stop_740_, lean_object* v_b_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; lean_object* v_res_744_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_740_);
lean_dec(v_stop_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_738_, v_i_boxed_742_, v_stop_boxed_743_, v_b_741_);
lean_dec_ref(v_as_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_745_, lean_object* v_s_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_get_size(v_ps_745_);
v___x_749_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
return v_s_746_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = lean_nat_dec_le(v___x_748_, v___x_748_);
if (v___x_750_ == 0)
{
if (v___x_749_ == 0)
{
return v_s_746_;
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_748_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_745_, v___x_751_, v___x_752_, v_s_746_);
return v___x_753_;
}
}
else
{
size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_748_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_745_, v___x_754_, v___x_755_, v_s_746_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_757_, v_s_758_);
lean_dec_ref(v_ps_757_);
return v_res_759_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_760_, size_t v_i_761_, size_t v_stop_762_, lean_object* v_b_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_eq(v_i_761_, v_stop_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; size_t v___x_767_; size_t v___x_768_; 
v___x_765_ = lean_array_uget_borrowed(v_as_760_, v_i_761_);
lean_inc(v___x_765_);
v___x_766_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_765_, v_b_763_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_761_, v___x_767_);
v_i_761_ = v___x_768_;
v_b_763_ = v___x_766_;
goto _start;
}
else
{
return v_b_763_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_760_ = stack[0].m_obj;
size_t v_i_761_ = stack[1].m_num;
size_t v_stop_762_ = stack[2].m_num;
lean_object* v_b_763_ = stack[3].m_obj;
lean_object* v_res_770_;
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_760_, v_i_761_, v_stop_762_, v_b_763_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_771_, lean_object* v_s_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_alts_771_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
return v_s_772_;
}
else
{
uint8_t v___x_776_; 
v___x_776_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_776_ == 0)
{
if (v___x_775_ == 0)
{
return v_s_772_;
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_774_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_771_, v___x_777_, v___x_778_, v_s_772_);
return v___x_779_;
}
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_774_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_771_, v___x_780_, v___x_781_, v_s_772_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_783_, lean_object* v_a_784_){
_start:
{
switch(lean_obj_tag(v_x_783_))
{
case 0:
{
lean_object* v_decl_785_; lean_object* v_k_786_; lean_object* v_type_787_; lean_object* v_value_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_decl_785_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_decl_785_);
v_k_786_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_k_786_);
lean_dec_ref_known(v_x_783_, 2);
v_type_787_ = lean_ctor_get(v_decl_785_, 2);
lean_inc_ref(v_type_787_);
v_value_788_ = lean_ctor_get(v_decl_785_, 3);
lean_inc(v_value_788_);
lean_dec_ref(v_decl_785_);
v___x_789_ = l_Lean_CollectLevelParams_visitExpr(v_type_787_, v_a_784_);
v___x_790_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_788_, v___x_789_);
v_x_783_ = v_k_786_;
v_a_784_ = v___x_790_;
goto _start;
}
case 3:
{
lean_object* v_args_792_; lean_object* v___x_793_; 
v_args_792_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_args_792_);
lean_dec_ref_known(v_x_783_, 2);
v___x_793_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_792_, v_a_784_);
lean_dec_ref(v_args_792_);
return v___x_793_;
}
case 4:
{
lean_object* v_cases_794_; lean_object* v_resultType_795_; lean_object* v_alts_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_cases_794_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_cases_794_);
lean_dec_ref_known(v_x_783_, 1);
v_resultType_795_ = lean_ctor_get(v_cases_794_, 1);
lean_inc_ref(v_resultType_795_);
v_alts_796_ = lean_ctor_get(v_cases_794_, 3);
lean_inc_ref(v_alts_796_);
lean_dec_ref(v_cases_794_);
v___x_797_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_795_, v_a_784_);
v___x_798_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_796_, v___x_797_);
lean_dec_ref(v_alts_796_);
return v___x_798_;
}
case 5:
{
lean_dec_ref_known(v_x_783_, 1);
return v_a_784_;
}
case 6:
{
lean_object* v_type_799_; lean_object* v___x_800_; 
v_type_799_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_type_799_);
lean_dec_ref_known(v_x_783_, 1);
v___x_800_ = l_Lean_CollectLevelParams_visitExpr(v_type_799_, v_a_784_);
return v___x_800_;
}
default: 
{
lean_object* v_decl_801_; lean_object* v_k_802_; lean_object* v_params_803_; lean_object* v_type_804_; lean_object* v_value_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_decl_801_ = lean_ctor_get(v_x_783_, 0);
lean_inc_ref(v_decl_801_);
v_k_802_ = lean_ctor_get(v_x_783_, 1);
lean_inc_ref(v_k_802_);
lean_dec_ref(v_x_783_);
v_params_803_ = lean_ctor_get(v_decl_801_, 2);
lean_inc_ref(v_params_803_);
v_type_804_ = lean_ctor_get(v_decl_801_, 3);
lean_inc_ref(v_type_804_);
v_value_805_ = lean_ctor_get(v_decl_801_, 4);
lean_inc_ref(v_value_805_);
lean_dec_ref(v_decl_801_);
v___x_806_ = l_Lean_CollectLevelParams_visitExpr(v_type_804_, v_a_784_);
v___x_807_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_803_, v___x_806_);
lean_dec_ref(v_params_803_);
v___x_808_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_805_, v___x_807_);
v_x_783_ = v_k_802_;
v_a_784_ = v___x_808_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_810_, lean_object* v_a_811_){
_start:
{
if (lean_obj_tag(v_alt_810_) == 0)
{
lean_object* v_params_812_; lean_object* v_code_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_params_812_ = lean_ctor_get(v_alt_810_, 1);
lean_inc_ref(v_params_812_);
v_code_813_ = lean_ctor_get(v_alt_810_, 2);
lean_inc_ref(v_code_813_);
lean_dec_ref_known(v_alt_810_, 3);
v___x_814_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_812_, v_a_811_);
lean_dec_ref(v_params_812_);
v___x_815_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_813_, v___x_814_);
return v___x_815_;
}
else
{
lean_object* v_code_816_; lean_object* v___x_817_; 
v_code_816_ = lean_ctor_get(v_alt_810_, 0);
lean_inc_ref(v_code_816_);
lean_dec_ref_known(v_alt_810_, 1);
v___x_817_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_816_, v_a_811_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_818_, lean_object* v_i_819_, lean_object* v_stop_820_, lean_object* v_b_821_){
_start:
{
size_t v_i_boxed_822_; size_t v_stop_boxed_823_; lean_object* v_res_824_; 
v_i_boxed_822_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_stop_boxed_823_ = lean_unbox_usize(v_stop_820_);
lean_dec(v_stop_820_);
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_818_, v_i_boxed_822_, v_stop_boxed_823_, v_b_821_);
lean_dec_ref(v_as_818_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_825_, lean_object* v_s_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_825_, v_s_826_);
lean_dec_ref(v_alts_825_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_828_, lean_object* v_a_829_){
_start:
{
if (lean_obj_tag(v_x_828_) == 0)
{
lean_object* v_code_830_; lean_object* v___x_831_; 
v_code_830_ = lean_ctor_get(v_x_828_, 0);
lean_inc_ref(v_code_830_);
lean_dec_ref_known(v_x_828_, 1);
v___x_831_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_830_, v_a_829_);
return v___x_831_;
}
else
{
lean_dec_ref_known(v_x_828_, 1);
return v_a_829_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_box(0);
v___x_833_ = lean_unsigned_to_nat(16u);
v___x_834_ = lean_mk_array(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_839_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_ctor_set(v___x_840_, 2, v___x_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_841_){
_start:
{
lean_object* v_toSignature_842_; lean_object* v_value_843_; uint8_t v_recursive_844_; lean_object* v_inlineAttr_x3f_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_870_; 
v_toSignature_842_ = lean_ctor_get(v_decl_841_, 0);
v_value_843_ = lean_ctor_get(v_decl_841_, 1);
v_recursive_844_ = lean_ctor_get_uint8(v_decl_841_, sizeof(void*)*3);
v_inlineAttr_x3f_845_ = lean_ctor_get(v_decl_841_, 2);
v_isSharedCheck_870_ = !lean_is_exclusive(v_decl_841_);
if (v_isSharedCheck_870_ == 0)
{
v___x_847_ = v_decl_841_;
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_inlineAttr_x3f_845_);
lean_inc(v_value_843_);
lean_inc(v_toSignature_842_);
lean_dec(v_decl_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_name_849_; lean_object* v_type_850_; lean_object* v_params_851_; uint8_t v_safe_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_868_; 
v_name_849_ = lean_ctor_get(v_toSignature_842_, 0);
v_type_850_ = lean_ctor_get(v_toSignature_842_, 2);
v_params_851_ = lean_ctor_get(v_toSignature_842_, 3);
v_safe_852_ = lean_ctor_get_uint8(v_toSignature_842_, sizeof(void*)*4);
v_isSharedCheck_868_ = !lean_is_exclusive(v_toSignature_842_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_toSignature_842_, 1);
lean_dec(v_unused_869_);
v___x_854_ = v_toSignature_842_;
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_params_851_);
lean_inc(v_type_850_);
lean_inc(v_name_849_);
lean_dec(v_toSignature_842_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_params_860_; lean_object* v_levelParams_861_; lean_object* v___x_863_; 
v___x_856_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_850_);
v___x_857_ = l_Lean_CollectLevelParams_visitExpr(v_type_850_, v___x_856_);
v___x_858_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_851_, v___x_857_);
lean_inc_ref(v_value_843_);
v___x_859_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_843_, v___x_858_);
v_params_860_ = lean_ctor_get(v___x_859_, 2);
lean_inc_ref(v_params_860_);
lean_dec_ref(v___x_859_);
v_levelParams_861_ = lean_array_to_list(v_params_860_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v_levelParams_861_);
v___x_863_ = v___x_854_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_name_849_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_levelParams_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_type_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_params_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*4, v_safe_852_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_863_);
v___x_865_ = v___x_847_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_value_843_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_inlineAttr_x3f_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_866_, sizeof(void*)*3, v_recursive_844_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
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
