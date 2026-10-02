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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object* v_a_104_, lean_object* v_x_105_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object* v_a_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_111_, v_x_112_);
lean_dec(v_x_112_);
lean_dec(v_a_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object* v_m_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v_size_118_; lean_object* v_buckets_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_165_; 
v_size_118_ = lean_ctor_get(v_m_115_, 0);
v_buckets_119_ = lean_ctor_get(v_m_115_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_m_115_);
if (v_isSharedCheck_165_ == 0)
{
v___x_121_ = v_m_115_;
v_isShared_122_ = v_isSharedCheck_165_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_buckets_119_);
lean_inc(v_size_118_);
lean_dec(v_m_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_165_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; uint64_t v___y_125_; 
v___x_123_ = lean_array_get_size(v_buckets_119_);
if (lean_obj_tag(v_a_116_) == 0)
{
uint64_t v___x_163_; 
v___x_163_ = 1723ULL;
v___y_125_ = v___x_163_;
goto v___jp_124_;
}
else
{
uint64_t v_hash_164_; 
v_hash_164_ = lean_ctor_get_uint64(v_a_116_, sizeof(void*)*2);
v___y_125_ = v_hash_164_;
goto v___jp_124_;
}
v___jp_124_:
{
uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v_fold_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; lean_object* v_bkt_137_; uint8_t v___x_138_; 
v___x_126_ = 32ULL;
v___x_127_ = lean_uint64_shift_right(v___y_125_, v___x_126_);
v_fold_128_ = lean_uint64_xor(v___y_125_, v___x_127_);
v___x_129_ = 16ULL;
v___x_130_ = lean_uint64_shift_right(v_fold_128_, v___x_129_);
v___x_131_ = lean_uint64_xor(v_fold_128_, v___x_130_);
v___x_132_ = lean_uint64_to_usize(v___x_131_);
v___x_133_ = lean_usize_of_nat(v___x_123_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_sub(v___x_133_, v___x_134_);
v___x_136_ = lean_usize_land(v___x_132_, v___x_135_);
v_bkt_137_ = lean_array_uget_borrowed(v_buckets_119_, v___x_136_);
v___x_138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_116_, v_bkt_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v_size_x27_140_; lean_object* v___x_141_; lean_object* v_buckets_x27_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v_size_x27_140_ = lean_nat_add(v_size_118_, v___x_139_);
lean_dec(v_size_118_);
lean_inc(v_bkt_137_);
v___x_141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_141_, 0, v_a_116_);
lean_ctor_set(v___x_141_, 1, v_b_117_);
lean_ctor_set(v___x_141_, 2, v_bkt_137_);
v_buckets_x27_142_ = lean_array_uset(v_buckets_119_, v___x_136_, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(4u);
v___x_144_ = lean_nat_mul(v_size_x27_140_, v___x_143_);
v___x_145_ = lean_unsigned_to_nat(3u);
v___x_146_ = lean_nat_div(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_array_get_size(v_buckets_x27_142_);
v___x_148_ = lean_nat_dec_le(v___x_146_, v___x_147_);
lean_dec(v___x_146_);
if (v___x_148_ == 0)
{
lean_object* v_val_149_; lean_object* v___x_151_; 
v_val_149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_buckets_x27_142_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_val_149_);
lean_ctor_set(v___x_121_, 0, v_size_x27_140_);
v___x_151_ = v___x_121_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_size_x27_140_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_val_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
else
{
lean_object* v___x_154_; 
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_buckets_x27_142_);
lean_ctor_set(v___x_121_, 0, v_size_x27_140_);
v___x_154_ = v___x_121_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_size_x27_140_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_buckets_x27_142_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v___x_156_; lean_object* v_buckets_x27_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
lean_inc(v_bkt_137_);
v___x_156_ = lean_box(0);
v_buckets_x27_157_ = lean_array_uset(v_buckets_119_, v___x_136_, v___x_156_);
v___x_158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_116_, v_b_117_, v_bkt_137_);
v___x_159_ = lean_array_uset(v_buckets_x27_157_, v___x_136_, v___x_158_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_159_);
v___x_161_ = v___x_121_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_118_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object* v_a_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_key_169_; lean_object* v_value_170_; lean_object* v_tail_171_; uint8_t v___x_172_; 
v_key_169_ = lean_ctor_get(v_x_167_, 0);
v_value_170_ = lean_ctor_get(v_x_167_, 1);
v_tail_171_ = lean_ctor_get(v_x_167_, 2);
v___x_172_ = lean_name_eq(v_key_169_, v_a_166_);
if (v___x_172_ == 0)
{
v_x_167_ = v_tail_171_;
goto _start;
}
else
{
lean_object* v___x_174_; 
lean_inc(v_value_170_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_value_170_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_175_, lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_175_, v_x_176_);
lean_dec(v_x_176_);
lean_dec(v_a_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_buckets_180_; lean_object* v___x_181_; uint64_t v___y_183_; 
v_buckets_180_ = lean_ctor_get(v_m_178_, 1);
v___x_181_ = lean_array_get_size(v_buckets_180_);
if (lean_obj_tag(v_a_179_) == 0)
{
uint64_t v___x_197_; 
v___x_197_ = 1723ULL;
v___y_183_ = v___x_197_;
goto v___jp_182_;
}
else
{
uint64_t v_hash_198_; 
v_hash_198_ = lean_ctor_get_uint64(v_a_179_, sizeof(void*)*2);
v___y_183_ = v_hash_198_;
goto v___jp_182_;
}
v___jp_182_:
{
uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v_fold_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_184_ = 32ULL;
v___x_185_ = lean_uint64_shift_right(v___y_183_, v___x_184_);
v_fold_186_ = lean_uint64_xor(v___y_183_, v___x_185_);
v___x_187_ = 16ULL;
v___x_188_ = lean_uint64_shift_right(v_fold_186_, v___x_187_);
v___x_189_ = lean_uint64_xor(v_fold_186_, v___x_188_);
v___x_190_ = lean_uint64_to_usize(v___x_189_);
v___x_191_ = lean_usize_of_nat(v___x_181_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_sub(v___x_191_, v___x_192_);
v___x_194_ = lean_usize_land(v___x_190_, v___x_193_);
v___x_195_ = lean_array_uget_borrowed(v_buckets_180_, v___x_194_);
v___x_196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_179_, v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg___boxed(lean_object* v_m_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_m_199_);
return v_res_201_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_208_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_209_ = lean_unsigned_to_nat(19u);
v___x_210_ = lean_unsigned_to_nat(55u);
v___x_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__3));
v___x_212_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_213_ = l_mkPanicMessageWithDecl(v___x_212_, v___x_211_, v___x_210_, v___x_209_, v___x_208_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normLevel(lean_object* v_u_214_, lean_object* v_a_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_Level_hasParam(v_u_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_u_214_);
lean_ctor_set(v___x_217_, 1, v_a_215_);
return v___x_217_;
}
else
{
switch(lean_obj_tag(v_u_214_))
{
case 0:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_u_214_);
lean_ctor_set(v___x_218_, 1, v_a_215_);
return v___x_218_;
}
case 1:
{
lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_236_; 
v_a_219_ = lean_ctor_get(v_u_214_, 0);
lean_inc(v_a_219_);
v___x_220_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_219_, v_a_215_);
v_fst_221_ = lean_ctor_get(v___x_220_, 0);
v_snd_222_ = lean_ctor_get(v___x_220_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_236_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snd_222_);
lean_inc(v_fst_221_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
size_t v___x_226_; size_t v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_ptr_addr(v_a_219_);
v___x_227_ = lean_ptr_addr(v_fst_221_);
v___x_228_ = lean_usize_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec_ref_known(v_u_214_, 1);
v___x_229_ = l_Lean_Level_succ___override(v_fst_221_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_229_);
v___x_231_ = v___x_224_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_snd_222_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
else
{
lean_object* v___x_234_; 
lean_dec(v_fst_221_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v_u_214_);
v___x_234_ = v___x_224_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_u_214_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_snd_222_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
case 2:
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_242_; lean_object* v_fst_243_; lean_object* v_snd_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_266_; 
v_a_237_ = lean_ctor_get(v_u_214_, 0);
v_a_238_ = lean_ctor_get(v_u_214_, 1);
lean_inc(v_a_237_);
v___x_239_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_237_, v_a_215_);
v_fst_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_fst_240_);
v_snd_241_ = lean_ctor_get(v___x_239_, 1);
lean_inc(v_snd_241_);
lean_dec_ref(v___x_239_);
lean_inc(v_a_238_);
v___x_242_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_238_, v_snd_241_);
v_fst_243_ = lean_ctor_get(v___x_242_, 0);
v_snd_244_ = lean_ctor_get(v___x_242_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_266_ == 0)
{
v___x_246_ = v___x_242_;
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_snd_244_);
lean_inc(v_fst_243_);
lean_dec(v___x_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_266_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
size_t v___x_248_; size_t v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_ptr_addr(v_a_237_);
v___x_249_ = lean_ptr_addr(v_fst_240_);
v___x_250_ = lean_usize_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec_ref_known(v_u_214_, 2);
v___x_251_ = l_Lean_mkLevelMax_x27(v_fst_240_, v_fst_243_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_251_);
v___x_253_ = v___x_246_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_244_);
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
size_t v___x_255_; size_t v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_ptr_addr(v_a_238_);
v___x_256_ = lean_ptr_addr(v_fst_243_);
v___x_257_ = lean_usize_dec_eq(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec_ref_known(v_u_214_, 2);
v___x_258_ = l_Lean_mkLevelMax_x27(v_fst_240_, v_fst_243_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_258_);
v___x_260_ = v___x_246_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_snd_244_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = l_Lean_simpLevelMax_x27(v_fst_240_, v_fst_243_, v_u_214_);
lean_dec_ref_known(v_u_214_, 2);
lean_dec(v_fst_243_);
lean_dec(v_fst_240_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_262_);
v___x_264_ = v___x_246_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_snd_244_);
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
case 3:
{
lean_object* v_a_267_; lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_296_; 
v_a_267_ = lean_ctor_get(v_u_214_, 0);
v_a_268_ = lean_ctor_get(v_u_214_, 1);
lean_inc(v_a_267_);
v___x_269_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_267_, v_a_215_);
v_fst_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_fst_270_);
v_snd_271_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_snd_271_);
lean_dec_ref(v___x_269_);
lean_inc(v_a_268_);
v___x_272_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_a_268_, v_snd_271_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
v_snd_274_ = lean_ctor_get(v___x_272_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_296_ == 0)
{
v___x_276_ = v___x_272_;
v_isShared_277_ = v_isSharedCheck_296_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snd_274_);
lean_inc(v_fst_273_);
lean_dec(v___x_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_296_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
size_t v___x_278_; size_t v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_ptr_addr(v_a_267_);
v___x_279_ = lean_ptr_addr(v_fst_270_);
v___x_280_ = lean_usize_dec_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec_ref_known(v_u_214_, 2);
v___x_281_ = l_Lean_mkLevelIMax_x27(v_fst_270_, v_fst_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_281_);
v___x_283_ = v___x_276_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_snd_274_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
size_t v___x_285_; size_t v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_ptr_addr(v_a_268_);
v___x_286_ = lean_ptr_addr(v_fst_273_);
v___x_287_ = lean_usize_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_290_; 
lean_dec_ref_known(v_u_214_, 2);
v___x_288_ = l_Lean_mkLevelIMax_x27(v_fst_270_, v_fst_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_288_);
v___x_290_ = v___x_276_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_snd_274_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = l_Lean_simpLevelIMax_x27(v_fst_270_, v_fst_273_, v_u_214_);
lean_dec_ref_known(v_u_214_, 2);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_292_);
v___x_294_ = v___x_276_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_snd_274_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
case 4:
{
lean_object* v_a_297_; lean_object* v_nextIdx_298_; lean_object* v_map_299_; lean_object* v_paramNames_300_; lean_object* v___x_301_; 
v_a_297_ = lean_ctor_get(v_u_214_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v_u_214_, 1);
v_nextIdx_298_ = lean_ctor_get(v_a_215_, 0);
v_map_299_ = lean_ctor_get(v_a_215_, 1);
v_paramNames_300_ = lean_ctor_get(v_a_215_, 2);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_map_299_, v_a_297_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_316_; 
lean_inc_ref(v_paramNames_300_);
lean_inc_ref(v_map_299_);
lean_inc(v_nextIdx_298_);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_215_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_317_ = lean_ctor_get(v_a_215_, 2);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_a_215_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_a_215_, 0);
lean_dec(v_unused_319_);
v___x_303_ = v_a_215_;
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_a_215_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_316_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_305_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_298_);
v___x_306_ = lean_name_append_index_after(v___x_305_, v_nextIdx_298_);
v___x_307_ = l_Lean_Level_param___override(v___x_306_);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_nextIdx_298_, v___x_308_);
lean_dec(v_nextIdx_298_);
lean_inc(v___x_307_);
lean_inc(v_a_297_);
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_299_, v_a_297_, v___x_307_);
v___x_311_ = lean_array_push(v_paramNames_300_, v_a_297_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 2, v___x_311_);
lean_ctor_set(v___x_303_, 1, v___x_310_);
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_313_ = v___x_303_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v___x_311_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_307_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
}
}
else
{
lean_object* v_val_320_; lean_object* v___x_321_; 
lean_dec(v_a_297_);
v_val_320_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_val_320_);
lean_dec_ref_known(v___x_301_, 1);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_val_320_);
lean_ctor_set(v___x_321_, 1, v_a_215_);
return v___x_321_;
}
}
default: 
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref_known(v_u_214_, 1);
v___x_322_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_323_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v___x_322_, v_a_215_);
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_324_, lean_object* v_m_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_325_, v_a_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_328_, lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_328_, v_m_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_332_, lean_object* v_m_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_333_, v_a_334_, v_b_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_337_, lean_object* v_a_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_a_338_, v_x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_341_, lean_object* v_a_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_341_, v_a_342_, v_x_343_);
lean_dec(v_x_343_);
lean_dec(v_a_342_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_345_, lean_object* v_a_346_, lean_object* v_x_347_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_a_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_349_, lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_349_, v_a_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec(v_a_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3(lean_object* v_00_u03b2_354_, lean_object* v_data_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3___redArg(v_data_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4(lean_object* v_00_u03b2_357_, lean_object* v_a_358_, lean_object* v_b_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__4___redArg(v_a_358_, v_b_359_, v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_362_, lean_object* v_i_363_, lean_object* v_source_364_, lean_object* v_target_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5___redArg(v_i_363_, v_source_364_, v_target_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__3_spec__5_spec__6___redArg(v_x_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_4908__overap_395_; lean_object* v___x_396_; 
v___f_373_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__0));
v___f_374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__1));
v___f_375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__2));
v___f_376_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__3));
v___f_377_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__4));
v___f_378_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__5));
v___f_379_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___closed__6));
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___f_373_);
lean_ctor_set(v___x_380_, 1, v___f_374_);
v___x_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___f_375_);
lean_ctor_set(v___x_381_, 2, v___f_376_);
lean_ctor_set(v___x_381_, 3, v___f_377_);
lean_ctor_set(v___x_381_, 4, v___f_378_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___f_379_);
lean_inc_ref_n(v___x_382_, 6);
v___f_383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_383_, 0, v___x_382_);
v___f_384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_384_, 0, v___x_382_);
v___f_385_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_385_, 0, v___x_382_);
v___f_386_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_386_, 0, v___x_382_);
v___x_387_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_387_, 0, lean_box(0));
lean_closure_set(v___x_387_, 1, lean_box(0));
lean_closure_set(v___x_387_, 2, v___x_382_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___f_383_);
v___x_389_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, lean_box(0));
lean_closure_set(v___x_389_, 2, v___x_382_);
v___x_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
lean_ctor_set(v___x_390_, 2, v___f_384_);
lean_ctor_set(v___x_390_, 3, v___f_385_);
lean_ctor_set(v___x_390_, 4, v___f_386_);
v___x_391_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, lean_box(0));
lean_closure_set(v___x_391_, 2, v___x_382_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = l_Lean_instInhabitedExpr;
v___x_394_ = l_instInhabitedOfMonad___redArg(v___x_392_, v___x_393_);
v___x_4908__overap_395_ = lean_panic_fn_borrowed(v___x_394_, v_msg_371_);
lean_dec(v___x_394_);
v___x_396_ = lean_apply_1(v___x_4908__overap_395_, v___y_372_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v___y_399_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = l_List_reverse___redArg(v_x_398_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___y_399_);
return v___x_401_;
}
else
{
lean_object* v_head_402_; lean_object* v_tail_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v_head_402_ = lean_ctor_get(v_x_397_, 0);
v_tail_403_ = lean_ctor_get(v_x_397_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_397_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v_x_397_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_tail_403_);
lean_inc(v_head_402_);
lean_dec(v_x_397_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_411_; 
v___x_407_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_402_, v___y_399_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_fst_408_);
v_snd_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_snd_409_);
lean_dec_ref(v___x_407_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_x_398_);
lean_ctor_set(v___x_405_, 0, v_fst_408_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fst_408_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_x_398_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v_x_397_ = v_tail_403_;
v_x_398_ = v___x_411_;
v___y_399_ = v_snd_409_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_417_ = lean_unsigned_to_nat(26u);
v___x_418_ = lean_unsigned_to_nat(79u);
v___x_419_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_420_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_421_ = l_mkPanicMessageWithDecl(v___x_420_, v___x_419_, v___x_418_, v___x_417_, v___x_416_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_422_, lean_object* v_a_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_Expr_hasLevelParam(v_e_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_e_422_);
lean_ctor_set(v___x_425_, 1, v_a_423_);
return v___x_425_;
}
else
{
switch(lean_obj_tag(v_e_422_))
{
case 4:
{
lean_object* v_declName_426_; lean_object* v_us_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_443_; 
v_declName_426_ = lean_ctor_get(v_e_422_, 0);
v_us_427_ = lean_ctor_get(v_e_422_, 1);
v___x_428_ = lean_box(0);
lean_inc(v_us_427_);
v___x_429_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_427_, v___x_428_, v_a_423_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
v_snd_431_ = lean_ctor_get(v___x_429_, 1);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_443_ == 0)
{
v___x_433_ = v___x_429_;
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_inc(v_fst_430_);
lean_dec(v___x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___x_435_; 
v___x_435_ = l_ptrEqList___redArg(v_us_427_, v_fst_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_declName_426_);
lean_dec_ref_known(v_e_422_, 2);
v___x_436_ = l_Lean_Expr_const___override(v_declName_426_, v_fst_430_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_snd_431_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
lean_object* v___x_441_; 
lean_dec(v_fst_430_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_e_422_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_431_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
case 3:
{
lean_object* v_u_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_461_; 
v_u_444_ = lean_ctor_get(v_e_422_, 0);
lean_inc(v_u_444_);
v___x_445_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_444_, v_a_423_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_461_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_461_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snd_447_);
lean_inc(v_fst_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_461_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_ptr_addr(v_u_444_);
v___x_452_ = lean_ptr_addr(v_fst_446_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec_ref_known(v_e_422_, 1);
v___x_454_ = l_Lean_Expr_sort___override(v_fst_446_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_447_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_fst_446_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_e_422_);
v___x_459_ = v___x_449_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_snd_447_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
case 5:
{
lean_object* v_fn_462_; lean_object* v_arg_463_; lean_object* v___x_464_; lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_467_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_490_; 
v_fn_462_ = lean_ctor_get(v_e_422_, 0);
v_arg_463_ = lean_ctor_get(v_e_422_, 1);
lean_inc_ref(v_fn_462_);
v___x_464_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_462_, v_a_423_);
v_fst_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_fst_465_);
v_snd_466_ = lean_ctor_get(v___x_464_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v___x_464_);
lean_inc_ref(v_arg_463_);
v___x_467_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_463_, v_snd_466_);
v_fst_468_ = lean_ctor_get(v___x_467_, 0);
v_snd_469_ = lean_ctor_get(v___x_467_, 1);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_490_ == 0)
{
v___x_471_ = v___x_467_;
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_inc(v_fst_468_);
lean_dec(v___x_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
size_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_ptr_addr(v_fn_462_);
v___x_474_ = lean_ptr_addr(v_fst_465_);
v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec_ref_known(v_e_422_, 2);
v___x_476_ = l_Lean_Expr_app___override(v_fst_465_, v_fst_468_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_476_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_snd_469_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_ptr_addr(v_arg_463_);
v___x_481_ = lean_ptr_addr(v_fst_468_);
v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec_ref_known(v_e_422_, 2);
v___x_483_ = l_Lean_Expr_app___override(v_fst_465_, v_fst_468_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_483_);
v___x_485_ = v___x_471_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_snd_469_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_fst_468_);
lean_dec(v_fst_465_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v_e_422_);
v___x_488_ = v___x_471_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_snd_469_);
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
case 8:
{
lean_object* v_declName_491_; lean_object* v_type_492_; lean_object* v_value_493_; lean_object* v_body_494_; uint8_t v_nondep_495_; lean_object* v___x_496_; lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_499_; lean_object* v_fst_500_; lean_object* v_snd_501_; lean_object* v___x_502_; lean_object* v_fst_503_; lean_object* v_snd_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_532_; 
v_declName_491_ = lean_ctor_get(v_e_422_, 0);
v_type_492_ = lean_ctor_get(v_e_422_, 1);
v_value_493_ = lean_ctor_get(v_e_422_, 2);
v_body_494_ = lean_ctor_get(v_e_422_, 3);
v_nondep_495_ = lean_ctor_get_uint8(v_e_422_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_492_);
v___x_496_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_492_, v_a_423_);
v_fst_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_fst_497_);
v_snd_498_ = lean_ctor_get(v___x_496_, 1);
lean_inc(v_snd_498_);
lean_dec_ref(v___x_496_);
lean_inc_ref(v_value_493_);
v___x_499_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_493_, v_snd_498_);
v_fst_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_fst_500_);
v_snd_501_ = lean_ctor_get(v___x_499_, 1);
lean_inc(v_snd_501_);
lean_dec_ref(v___x_499_);
lean_inc_ref(v_body_494_);
v___x_502_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_494_, v_snd_501_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
v_snd_504_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_532_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_532_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_snd_504_);
lean_inc(v_fst_503_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_532_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_ptr_addr(v_type_492_);
v___x_509_ = lean_ptr_addr(v_fst_497_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_declName_491_);
lean_dec_ref_known(v_e_422_, 4);
v___x_511_ = l_Lean_Expr_letE___override(v_declName_491_, v_fst_497_, v_fst_500_, v_fst_503_, v_nondep_495_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_511_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_snd_504_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_ptr_addr(v_value_493_);
v___x_516_ = lean_ptr_addr(v_fst_500_);
v___x_517_ = lean_usize_dec_eq(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_declName_491_);
lean_dec_ref_known(v_e_422_, 4);
v___x_518_ = l_Lean_Expr_letE___override(v_declName_491_, v_fst_497_, v_fst_500_, v_fst_503_, v_nondep_495_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_518_);
v___x_520_ = v___x_506_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_504_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
size_t v___x_522_; size_t v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_ptr_addr(v_body_494_);
v___x_523_ = lean_ptr_addr(v_fst_503_);
v___x_524_ = lean_usize_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_inc(v_declName_491_);
lean_dec_ref_known(v_e_422_, 4);
v___x_525_ = l_Lean_Expr_letE___override(v_declName_491_, v_fst_497_, v_fst_500_, v_fst_503_, v_nondep_495_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_525_);
v___x_527_ = v___x_506_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_snd_504_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_530_; 
lean_dec(v_fst_503_);
lean_dec(v_fst_500_);
lean_dec(v_fst_497_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v_e_422_);
v___x_530_ = v___x_506_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_snd_504_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_533_; lean_object* v_binderType_534_; lean_object* v_body_535_; uint8_t v_binderInfo_536_; lean_object* v___x_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_568_; 
v_binderName_533_ = lean_ctor_get(v_e_422_, 0);
v_binderType_534_ = lean_ctor_get(v_e_422_, 1);
v_body_535_ = lean_ctor_get(v_e_422_, 2);
v_binderInfo_536_ = lean_ctor_get_uint8(v_e_422_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_534_);
v___x_537_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_534_, v_a_423_);
v_fst_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_fst_538_);
v_snd_539_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_snd_539_);
lean_dec_ref(v___x_537_);
lean_inc_ref(v_body_535_);
v___x_540_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_535_, v_snd_539_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_568_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_568_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_568_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
size_t v___x_546_; size_t v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_ptr_addr(v_binderType_534_);
v___x_547_ = lean_ptr_addr(v_fst_538_);
v___x_548_ = lean_usize_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_inc(v_binderName_533_);
lean_dec_ref_known(v_e_422_, 3);
v___x_549_ = l_Lean_Expr_forallE___override(v_binderName_533_, v_fst_538_, v_fst_541_, v_binderInfo_536_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_549_);
v___x_551_ = v___x_544_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_snd_542_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
size_t v___x_553_; size_t v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_ptr_addr(v_body_535_);
v___x_554_ = lean_ptr_addr(v_fst_541_);
v___x_555_ = lean_usize_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_558_; 
lean_inc(v_binderName_533_);
lean_dec_ref_known(v_e_422_, 3);
v___x_556_ = l_Lean_Expr_forallE___override(v_binderName_533_, v_fst_538_, v_fst_541_, v_binderInfo_536_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_556_);
v___x_558_ = v___x_544_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_snd_542_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
uint8_t v___x_560_; 
v___x_560_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_536_, v_binderInfo_536_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_inc(v_binderName_533_);
lean_dec_ref_known(v_e_422_, 3);
v___x_561_ = l_Lean_Expr_forallE___override(v_binderName_533_, v_fst_538_, v_fst_541_, v_binderInfo_536_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_561_);
v___x_563_ = v___x_544_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_snd_542_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v_fst_541_);
lean_dec(v_fst_538_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v_e_422_);
v___x_566_ = v___x_544_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_542_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_569_; lean_object* v_binderType_570_; lean_object* v_body_571_; uint8_t v_binderInfo_572_; lean_object* v___x_573_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_604_; 
v_binderName_569_ = lean_ctor_get(v_e_422_, 0);
v_binderType_570_ = lean_ctor_get(v_e_422_, 1);
v_body_571_ = lean_ctor_get(v_e_422_, 2);
v_binderInfo_572_ = lean_ctor_get_uint8(v_e_422_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_570_);
v___x_573_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_570_, v_a_423_);
v_fst_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_fst_574_);
v_snd_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_snd_575_);
lean_dec_ref(v___x_573_);
lean_inc_ref(v_body_571_);
v___x_576_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_571_, v_snd_575_);
v_fst_577_ = lean_ctor_get(v___x_576_, 0);
v_snd_578_ = lean_ctor_get(v___x_576_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_604_ == 0)
{
v___x_580_ = v___x_576_;
v_isShared_581_ = v_isSharedCheck_604_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snd_578_);
lean_inc(v_fst_577_);
lean_dec(v___x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_604_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_ptr_addr(v_binderType_570_);
v___x_583_ = lean_ptr_addr(v_fst_574_);
v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_587_; 
lean_inc(v_binderName_569_);
lean_dec_ref_known(v_e_422_, 3);
v___x_585_ = l_Lean_Expr_lam___override(v_binderName_569_, v_fst_574_, v_fst_577_, v_binderInfo_572_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_585_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_snd_578_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
size_t v___x_589_; size_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_ptr_addr(v_body_571_);
v___x_590_ = lean_ptr_addr(v_fst_577_);
v___x_591_ = lean_usize_dec_eq(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_inc(v_binderName_569_);
lean_dec_ref_known(v_e_422_, 3);
v___x_592_ = l_Lean_Expr_lam___override(v_binderName_569_, v_fst_574_, v_fst_577_, v_binderInfo_572_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_592_);
v___x_594_ = v___x_580_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_snd_578_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_572_, v_binderInfo_572_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_inc(v_binderName_569_);
lean_dec_ref_known(v_e_422_, 3);
v___x_597_ = l_Lean_Expr_lam___override(v_binderName_569_, v_fst_574_, v_fst_577_, v_binderInfo_572_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_597_);
v___x_599_ = v___x_580_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_snd_578_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v_fst_577_);
lean_dec(v_fst_574_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_e_422_);
v___x_602_ = v___x_580_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_snd_578_);
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
}
}
case 10:
{
lean_object* v_data_605_; lean_object* v_expr_606_; lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_623_; 
v_data_605_ = lean_ctor_get(v_e_422_, 0);
v_expr_606_ = lean_ctor_get(v_e_422_, 1);
lean_inc_ref(v_expr_606_);
v___x_607_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_606_, v_a_423_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
v_snd_609_ = lean_ctor_get(v___x_607_, 1);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_611_ = v___x_607_;
v_isShared_612_ = v_isSharedCheck_623_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snd_609_);
lean_inc(v_fst_608_);
lean_dec(v___x_607_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_623_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
size_t v___x_613_; size_t v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_ptr_addr(v_expr_606_);
v___x_614_ = lean_ptr_addr(v_fst_608_);
v___x_615_ = lean_usize_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_618_; 
lean_inc(v_data_605_);
lean_dec_ref_known(v_e_422_, 2);
v___x_616_ = l_Lean_Expr_mdata___override(v_data_605_, v_fst_608_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_616_);
v___x_618_ = v___x_611_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_snd_609_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_fst_608_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_e_422_);
v___x_621_ = v___x_611_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_snd_609_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
case 11:
{
lean_object* v_typeName_624_; lean_object* v_idx_625_; lean_object* v_struct_626_; lean_object* v___x_627_; lean_object* v_fst_628_; lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_643_; 
v_typeName_624_ = lean_ctor_get(v_e_422_, 0);
v_idx_625_ = lean_ctor_get(v_e_422_, 1);
v_struct_626_ = lean_ctor_get(v_e_422_, 2);
lean_inc_ref(v_struct_626_);
v___x_627_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_626_, v_a_423_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
v_snd_629_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_643_ == 0)
{
v___x_631_ = v___x_627_;
v_isShared_632_ = v_isSharedCheck_643_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_inc(v_fst_628_);
lean_dec(v___x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_643_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_ptr_addr(v_struct_626_);
v___x_634_ = lean_ptr_addr(v_fst_628_);
v___x_635_ = lean_usize_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_638_; 
lean_inc(v_idx_625_);
lean_inc(v_typeName_624_);
lean_dec_ref_known(v_e_422_, 3);
v___x_636_ = l_Lean_Expr_proj___override(v_typeName_624_, v_idx_625_, v_fst_628_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_636_);
v___x_638_ = v___x_631_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_snd_629_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v___x_641_; 
lean_dec(v_fst_628_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_e_422_);
v___x_641_ = v___x_631_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_e_422_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_snd_629_);
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
case 2:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref_known(v_e_422_, 1);
v___x_644_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_645_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_644_, v_a_423_);
return v___x_645_;
}
default: 
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_e_422_);
lean_ctor_set(v___x_646_, 1, v_a_423_);
return v___x_646_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_box(0);
v___x_648_ = lean_unsigned_to_nat(16u);
v___x_649_ = lean_mk_array(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_655_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_656_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___x_656_);
lean_ctor_set(v___x_658_, 2, v___x_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_snd_662_; lean_object* v_fst_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v___x_660_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__3, &l_Lean_Compiler_LCNF_normLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__3);
v___x_661_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_659_, v___x_660_);
v_snd_662_ = lean_ctor_get(v___x_661_, 1);
v_fst_663_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_672_ == 0)
{
v___x_665_ = v___x_661_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_663_);
lean_dec(v___x_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_paramNames_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_paramNames_667_ = lean_ctor_get(v_snd_662_, 2);
lean_inc_ref(v_paramNames_667_);
lean_dec(v_snd_662_);
v___x_668_ = lean_array_to_list(v_paramNames_667_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_fst_663_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_CollectLevelParams_visitExpr(v_type_673_, v_a_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_676_, lean_object* v_a_677_){
_start:
{
if (lean_obj_tag(v_arg_676_) == 2)
{
lean_object* v_expr_678_; lean_object* v___x_679_; 
v_expr_678_ = lean_ctor_get(v_arg_676_, 0);
lean_inc_ref(v_expr_678_);
lean_dec_ref_known(v_arg_676_, 1);
v___x_679_ = l_Lean_CollectLevelParams_visitExpr(v_expr_678_, v_a_677_);
return v___x_679_;
}
else
{
lean_dec(v_arg_676_);
return v_a_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; size_t v___x_687_; size_t v___x_688_; 
v___x_685_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
lean_inc(v___x_685_);
v___x_686_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_685_, v_b_683_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_add(v_i_681_, v___x_687_);
v_i_681_ = v___x_688_;
v_b_683_ = v___x_686_;
goto _start;
}
else
{
return v_b_683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_690_, lean_object* v_i_691_, lean_object* v_stop_692_, lean_object* v_b_693_){
_start:
{
size_t v_i_boxed_694_; size_t v_stop_boxed_695_; lean_object* v_res_696_; 
v_i_boxed_694_ = lean_unbox_usize(v_i_691_);
lean_dec(v_i_691_);
v_stop_boxed_695_ = lean_unbox_usize(v_stop_692_);
lean_dec(v_stop_692_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_690_, v_i_boxed_694_, v_stop_boxed_695_, v_b_693_);
lean_dec_ref(v_as_690_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_697_, lean_object* v_s_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_array_get_size(v_args_697_);
v___x_701_ = lean_nat_dec_lt(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
return v_s_698_;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = lean_nat_dec_le(v___x_700_, v___x_700_);
if (v___x_702_ == 0)
{
if (v___x_701_ == 0)
{
return v_s_698_;
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_700_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_697_, v___x_703_, v___x_704_, v_s_698_);
return v___x_705_;
}
}
else
{
size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_700_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_697_, v___x_706_, v___x_707_, v_s_698_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_709_, lean_object* v_s_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_709_, v_s_710_);
lean_dec_ref(v_args_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_712_, lean_object* v_a_713_){
_start:
{
switch(lean_obj_tag(v_e_712_))
{
case 3:
{
lean_object* v_us_714_; lean_object* v_args_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_us_714_ = lean_ctor_get(v_e_712_, 1);
lean_inc(v_us_714_);
v_args_715_ = lean_ctor_get(v_e_712_, 2);
lean_inc_ref(v_args_715_);
lean_dec_ref_known(v_e_712_, 3);
v___x_716_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_715_, v_a_713_);
lean_dec_ref(v_args_715_);
v___x_717_ = l_Lean_CollectLevelParams_visitLevels(v_us_714_, v___x_716_);
return v___x_717_;
}
case 4:
{
lean_object* v_args_718_; lean_object* v___x_719_; 
v_args_718_ = lean_ctor_get(v_e_712_, 1);
lean_inc_ref(v_args_718_);
lean_dec_ref_known(v_e_712_, 2);
v___x_719_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_718_, v_a_713_);
lean_dec_ref(v_args_718_);
return v___x_719_;
}
default: 
{
lean_dec(v_e_712_);
return v_a_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_type_722_; lean_object* v___x_723_; 
v_type_722_ = lean_ctor_get(v_p_720_, 2);
lean_inc_ref(v_type_722_);
lean_dec_ref(v_p_720_);
v___x_723_ = l_Lean_CollectLevelParams_visitExpr(v_type_722_, v_a_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_724_, size_t v_i_725_, size_t v_stop_726_, lean_object* v_b_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = lean_usize_dec_eq(v_i_725_, v_stop_726_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; size_t v___x_731_; size_t v___x_732_; 
v___x_729_ = lean_array_uget_borrowed(v_as_724_, v_i_725_);
lean_inc(v___x_729_);
v___x_730_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_729_, v_b_727_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_725_, v___x_731_);
v_i_725_ = v___x_732_;
v_b_727_ = v___x_730_;
goto _start;
}
else
{
return v_b_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_734_, lean_object* v_i_735_, lean_object* v_stop_736_, lean_object* v_b_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_736_);
lean_dec(v_stop_736_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_734_, v_i_boxed_738_, v_stop_boxed_739_, v_b_737_);
lean_dec_ref(v_as_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_741_, lean_object* v_s_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_array_get_size(v_ps_741_);
v___x_745_ = lean_nat_dec_lt(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
return v_s_742_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v___x_744_, v___x_744_);
if (v___x_746_ == 0)
{
if (v___x_745_ == 0)
{
return v_s_742_;
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_744_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_741_, v___x_747_, v___x_748_, v_s_742_);
return v___x_749_;
}
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_744_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_741_, v___x_750_, v___x_751_, v_s_742_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_753_, lean_object* v_s_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_753_, v_s_754_);
lean_dec_ref(v_ps_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_756_, size_t v_i_757_, size_t v_stop_758_, lean_object* v_b_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_757_, v_stop_758_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; 
v___x_761_ = lean_array_uget_borrowed(v_as_756_, v_i_757_);
lean_inc(v___x_761_);
v___x_762_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_761_, v_b_759_);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_757_, v___x_763_);
v_i_757_ = v___x_764_;
v_b_759_ = v___x_762_;
goto _start;
}
else
{
return v_b_759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_766_, lean_object* v_s_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_alts_766_);
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
return v_s_767_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = lean_nat_dec_le(v___x_769_, v___x_769_);
if (v___x_771_ == 0)
{
if (v___x_770_ == 0)
{
return v_s_767_;
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_769_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_766_, v___x_772_, v___x_773_, v_s_767_);
return v___x_774_;
}
}
else
{
size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_769_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_766_, v___x_775_, v___x_776_, v_s_767_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_778_, lean_object* v_a_779_){
_start:
{
switch(lean_obj_tag(v_x_778_))
{
case 0:
{
lean_object* v_decl_780_; lean_object* v_k_781_; lean_object* v_type_782_; lean_object* v_value_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_decl_780_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_decl_780_);
v_k_781_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_k_781_);
lean_dec_ref_known(v_x_778_, 2);
v_type_782_ = lean_ctor_get(v_decl_780_, 2);
lean_inc_ref(v_type_782_);
v_value_783_ = lean_ctor_get(v_decl_780_, 3);
lean_inc(v_value_783_);
lean_dec_ref(v_decl_780_);
v___x_784_ = l_Lean_CollectLevelParams_visitExpr(v_type_782_, v_a_779_);
v___x_785_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_783_, v___x_784_);
v_x_778_ = v_k_781_;
v_a_779_ = v___x_785_;
goto _start;
}
case 3:
{
lean_object* v_args_787_; lean_object* v___x_788_; 
v_args_787_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_args_787_);
lean_dec_ref_known(v_x_778_, 2);
v___x_788_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_787_, v_a_779_);
lean_dec_ref(v_args_787_);
return v___x_788_;
}
case 4:
{
lean_object* v_cases_789_; lean_object* v_resultType_790_; lean_object* v_alts_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_cases_789_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_cases_789_);
lean_dec_ref_known(v_x_778_, 1);
v_resultType_790_ = lean_ctor_get(v_cases_789_, 1);
lean_inc_ref(v_resultType_790_);
v_alts_791_ = lean_ctor_get(v_cases_789_, 3);
lean_inc_ref(v_alts_791_);
lean_dec_ref(v_cases_789_);
v___x_792_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_790_, v_a_779_);
v___x_793_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_791_, v___x_792_);
lean_dec_ref(v_alts_791_);
return v___x_793_;
}
case 5:
{
lean_dec_ref_known(v_x_778_, 1);
return v_a_779_;
}
case 6:
{
lean_object* v_type_794_; lean_object* v___x_795_; 
v_type_794_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_type_794_);
lean_dec_ref_known(v_x_778_, 1);
v___x_795_ = l_Lean_CollectLevelParams_visitExpr(v_type_794_, v_a_779_);
return v___x_795_;
}
default: 
{
lean_object* v_decl_796_; lean_object* v_k_797_; lean_object* v_params_798_; lean_object* v_type_799_; lean_object* v_value_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_decl_796_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_decl_796_);
v_k_797_ = lean_ctor_get(v_x_778_, 1);
lean_inc_ref(v_k_797_);
lean_dec_ref(v_x_778_);
v_params_798_ = lean_ctor_get(v_decl_796_, 2);
lean_inc_ref(v_params_798_);
v_type_799_ = lean_ctor_get(v_decl_796_, 3);
lean_inc_ref(v_type_799_);
v_value_800_ = lean_ctor_get(v_decl_796_, 4);
lean_inc_ref(v_value_800_);
lean_dec_ref(v_decl_796_);
v___x_801_ = l_Lean_CollectLevelParams_visitExpr(v_type_799_, v_a_779_);
v___x_802_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_798_, v___x_801_);
lean_dec_ref(v_params_798_);
v___x_803_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_800_, v___x_802_);
v_x_778_ = v_k_797_;
v_a_779_ = v___x_803_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_805_, lean_object* v_a_806_){
_start:
{
if (lean_obj_tag(v_alt_805_) == 0)
{
lean_object* v_params_807_; lean_object* v_code_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_params_807_ = lean_ctor_get(v_alt_805_, 1);
lean_inc_ref(v_params_807_);
v_code_808_ = lean_ctor_get(v_alt_805_, 2);
lean_inc_ref(v_code_808_);
lean_dec_ref_known(v_alt_805_, 3);
v___x_809_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_807_, v_a_806_);
lean_dec_ref(v_params_807_);
v___x_810_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_808_, v___x_809_);
return v___x_810_;
}
else
{
lean_object* v_code_811_; lean_object* v___x_812_; 
v_code_811_ = lean_ctor_get(v_alt_805_, 0);
lean_inc_ref(v_code_811_);
lean_dec_ref_known(v_alt_805_, 1);
v___x_812_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_811_, v_a_806_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_813_, lean_object* v_i_814_, lean_object* v_stop_815_, lean_object* v_b_816_){
_start:
{
size_t v_i_boxed_817_; size_t v_stop_boxed_818_; lean_object* v_res_819_; 
v_i_boxed_817_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_stop_boxed_818_ = lean_unbox_usize(v_stop_815_);
lean_dec(v_stop_815_);
v_res_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_813_, v_i_boxed_817_, v_stop_boxed_818_, v_b_816_);
lean_dec_ref(v_as_813_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_820_, lean_object* v_s_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_820_, v_s_821_);
lean_dec_ref(v_alts_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_823_, lean_object* v_a_824_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_code_825_; lean_object* v___x_826_; 
v_code_825_ = lean_ctor_get(v_x_823_, 0);
lean_inc_ref(v_code_825_);
lean_dec_ref_known(v_x_823_, 1);
v___x_826_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_825_, v_a_824_);
return v___x_826_;
}
else
{
lean_dec_ref_known(v_x_823_, 1);
return v_a_824_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
v___x_828_ = lean_unsigned_to_nat(16u);
v___x_829_ = lean_mk_array(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__2));
v___x_834_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
lean_ctor_set(v___x_835_, 2, v___x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_836_){
_start:
{
lean_object* v_toSignature_837_; lean_object* v_value_838_; uint8_t v_recursive_839_; lean_object* v_inlineAttr_x3f_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_865_; 
v_toSignature_837_ = lean_ctor_get(v_decl_836_, 0);
v_value_838_ = lean_ctor_get(v_decl_836_, 1);
v_recursive_839_ = lean_ctor_get_uint8(v_decl_836_, sizeof(void*)*3);
v_inlineAttr_x3f_840_ = lean_ctor_get(v_decl_836_, 2);
v_isSharedCheck_865_ = !lean_is_exclusive(v_decl_836_);
if (v_isSharedCheck_865_ == 0)
{
v___x_842_ = v_decl_836_;
v_isShared_843_ = v_isSharedCheck_865_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_inlineAttr_x3f_840_);
lean_inc(v_value_838_);
lean_inc(v_toSignature_837_);
lean_dec(v_decl_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_865_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_name_844_; lean_object* v_type_845_; lean_object* v_params_846_; uint8_t v_safe_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_863_; 
v_name_844_ = lean_ctor_get(v_toSignature_837_, 0);
v_type_845_ = lean_ctor_get(v_toSignature_837_, 2);
v_params_846_ = lean_ctor_get(v_toSignature_837_, 3);
v_safe_847_ = lean_ctor_get_uint8(v_toSignature_837_, sizeof(void*)*4);
v_isSharedCheck_863_ = !lean_is_exclusive(v_toSignature_837_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_toSignature_837_, 1);
lean_dec(v_unused_864_);
v___x_849_ = v_toSignature_837_;
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_params_846_);
lean_inc(v_type_845_);
lean_inc(v_name_844_);
lean_dec(v_toSignature_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_params_855_; lean_object* v_levelParams_856_; lean_object* v___x_858_; 
v___x_851_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
lean_inc_ref(v_type_845_);
v___x_852_ = l_Lean_CollectLevelParams_visitExpr(v_type_845_, v___x_851_);
v___x_853_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_846_, v___x_852_);
lean_inc_ref(v_value_838_);
v___x_854_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_838_, v___x_853_);
v_params_855_ = lean_ctor_get(v___x_854_, 2);
lean_inc_ref(v_params_855_);
lean_dec_ref(v___x_854_);
v_levelParams_856_ = lean_array_to_list(v_params_855_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v_levelParams_856_);
v___x_858_ = v___x_849_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_name_844_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_levelParams_856_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_type_845_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_params_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_862_, sizeof(void*)*4, v_safe_847_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_858_);
v___x_860_ = v___x_842_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_value_838_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_inlineAttr_x3f_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3, v_recursive_839_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
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
