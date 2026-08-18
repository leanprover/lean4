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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__5 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__6 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_normLevelParams___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__2;
static const lean_array_object l_Lean_Compiler_LCNF_normLevelParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_normLevelParams___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_normLevelParams___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_normLevelParams___closed__4;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3(lean_object* v_msg_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_4435__overap_32_; lean_object* v___x_33_; 
v___f_10_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__0));
v___f_11_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__1));
v___f_12_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__2));
v___f_13_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__3));
v___f_14_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__4));
v___f_15_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__5));
v___f_16_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__6));
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
v___x_4435__overap_32_ = lean_panic_fn_borrowed(v___x_31_, v_msg_8_);
lean_dec(v___x_31_);
v___x_33_ = lean_apply_1(v___x_4435__overap_32_, v___y_9_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(lean_object* v_m_34_, lean_object* v_query_35_, lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_zero_39_; uint8_t v_isZero_40_; 
v_zero_39_ = lean_unsigned_to_nat(0u);
v_isZero_40_ = lean_nat_dec_eq(v_x_37_, v_zero_39_);
if (v_isZero_40_ == 1)
{
lean_dec(v_x_38_);
lean_dec(v_x_37_);
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(2);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_val_42_ = lean_ctor_get(v_x_36_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_36_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v_x_36_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_val_42_);
lean_dec(v_x_36_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_val_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v_keyArray_50_; lean_object* v_valueArray_51_; lean_object* v___x_52_; uint8_t v_isSome_53_; 
v_keyArray_50_ = lean_ctor_get(v_m_34_, 1);
v_valueArray_51_ = lean_ctor_get(v_m_34_, 2);
v___x_52_ = lean_array_fget_borrowed(v_keyArray_50_, v_x_38_);
v_isSome_53_ = lean_noption_is_some(v___x_52_);
if (v_isSome_53_ == 0)
{
lean_dec(v_x_37_);
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_x_38_);
return v___x_54_;
}
else
{
lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
lean_dec(v_x_38_);
v_val_55_ = lean_ctor_get(v_x_36_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v_x_36_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v_x_36_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v_x_36_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_val_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
else
{
lean_object* v_one_63_; lean_object* v_n_64_; lean_object* v___y_66_; 
v_one_63_ = lean_unsigned_to_nat(1u);
v_n_64_ = lean_nat_sub(v_x_37_, v_one_63_);
lean_dec(v_x_37_);
if (v_isSome_53_ == 0)
{
goto v___jp_72_;
}
else
{
lean_object* v___x_74_; uint8_t v_isSome_75_; 
v___x_74_ = lean_array_fget_borrowed(v_valueArray_51_, v_x_38_);
v_isSome_75_ = lean_noption_is_some(v___x_74_);
if (v_isSome_75_ == 0)
{
goto v___jp_72_;
}
else
{
lean_object* v_val_76_; uint8_t v___x_77_; 
lean_inc(v___x_52_);
v_val_76_ = lean_noption_get(v___x_52_);
v___x_77_ = lean_name_eq(v_val_76_, v_query_35_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
lean_dec(v_val_76_);
v___x_78_ = lean_array_get_size(v_keyArray_50_);
v___x_79_ = lean_nat_add(v_x_38_, v_one_63_);
lean_dec(v_x_38_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v___x_78_);
if (v___x_80_ == 0)
{
lean_dec(v___x_79_);
v_x_37_ = v_n_64_;
v_x_38_ = v_zero_39_;
goto _start;
}
else
{
v_x_37_ = v_n_64_;
v_x_38_ = v___x_79_;
goto _start;
}
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; 
lean_dec(v_n_64_);
lean_dec(v_x_36_);
lean_inc(v___x_74_);
v_val_83_ = lean_noption_get(v___x_74_);
v___x_84_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_84_, 0, v_x_38_);
lean_ctor_set(v___x_84_, 1, v_val_76_);
lean_ctor_set(v___x_84_, 2, v_val_83_);
return v___x_84_;
}
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_array_get_size(v_keyArray_50_);
v___x_68_ = lean_nat_add(v_x_38_, v_one_63_);
lean_dec(v_x_38_);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v___x_67_);
if (v___x_69_ == 0)
{
lean_dec(v___x_68_);
v_x_36_ = v___y_66_;
v_x_37_ = v_n_64_;
v_x_38_ = v_zero_39_;
goto _start;
}
else
{
v_x_36_ = v___y_66_;
v_x_37_ = v_n_64_;
v_x_38_ = v___x_68_;
goto _start;
}
}
v___jp_72_:
{
if (lean_obj_tag(v_x_36_) == 0)
{
lean_object* v___x_73_; 
lean_inc(v_x_38_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_x_38_);
v___y_66_ = v___x_73_;
goto v___jp_65_;
}
else
{
v___y_66_ = v_x_36_;
goto v___jp_65_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg___boxed(lean_object* v_m_85_, lean_object* v_query_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_m_85_, v_query_86_, v_x_87_, v_x_88_, v_x_89_);
lean_dec(v_query_86_);
lean_dec_ref(v_m_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(lean_object* v_m_91_, lean_object* v_query_92_){
_start:
{
lean_object* v_keyArray_93_; lean_object* v___x_94_; uint64_t v___y_96_; 
v_keyArray_93_ = lean_ctor_get(v_m_91_, 1);
v___x_94_ = lean_array_get_size(v_keyArray_93_);
if (lean_obj_tag(v_query_92_) == 0)
{
uint64_t v___x_111_; 
v___x_111_ = 1723ULL;
v___y_96_ = v___x_111_;
goto v___jp_95_;
}
else
{
uint64_t v_hash_112_; 
v_hash_112_ = lean_ctor_get_uint64(v_query_92_, sizeof(void*)*2);
v___y_96_ = v_hash_112_;
goto v___jp_95_;
}
v___jp_95_:
{
uint64_t v___x_97_; uint64_t v___x_98_; uint64_t v_fold_99_; uint64_t v___x_100_; uint64_t v___x_101_; uint64_t v___x_102_; size_t v___x_103_; size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_97_ = 32ULL;
v___x_98_ = lean_uint64_shift_right(v___y_96_, v___x_97_);
v_fold_99_ = lean_uint64_xor(v___y_96_, v___x_98_);
v___x_100_ = 16ULL;
v___x_101_ = lean_uint64_shift_right(v_fold_99_, v___x_100_);
v___x_102_ = lean_uint64_xor(v_fold_99_, v___x_101_);
v___x_103_ = lean_uint64_to_usize(v___x_102_);
v___x_104_ = lean_usize_of_nat(v___x_94_);
v___x_105_ = ((size_t)1ULL);
v___x_106_ = lean_usize_sub(v___x_104_, v___x_105_);
v___x_107_ = lean_usize_land(v___x_103_, v___x_106_);
v___x_108_ = lean_usize_to_nat(v___x_107_);
v___x_109_ = lean_box(0);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_m_91_, v_query_92_, v___x_109_, v___x_94_, v___x_108_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg___boxed(lean_object* v_m_113_, lean_object* v_query_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_113_, v_query_114_);
lean_dec(v_query_114_);
lean_dec_ref(v_m_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg(lean_object* v_b_116_, lean_object* v_acc_117_, lean_object* v_i_118_){
_start:
{
lean_object* v___y_120_; lean_object* v_keyArray_128_; lean_object* v_valueArray_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_keyArray_128_ = lean_ctor_get(v_b_116_, 1);
v_valueArray_129_ = lean_ctor_get(v_b_116_, 2);
v___x_130_ = lean_array_get_size(v_keyArray_128_);
v___x_131_ = lean_nat_dec_lt(v_i_118_, v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v_i_118_);
return v_acc_117_;
}
else
{
lean_object* v___x_132_; uint8_t v_isSome_133_; 
v___x_132_ = lean_array_fget_borrowed(v_keyArray_128_, v_i_118_);
v_isSome_133_ = lean_noption_is_some(v___x_132_);
if (v_isSome_133_ == 0)
{
goto v___jp_124_;
}
else
{
lean_object* v___x_134_; uint8_t v_isSome_135_; 
v___x_134_ = lean_array_fget_borrowed(v_valueArray_129_, v_i_118_);
v_isSome_135_ = lean_noption_is_some(v___x_134_);
if (v_isSome_135_ == 0)
{
goto v___jp_124_;
}
else
{
lean_object* v_val_136_; lean_object* v_val_137_; lean_object* v_i_139_; lean_object* v___x_144_; 
lean_inc(v___x_132_);
v_val_136_ = lean_noption_get(v___x_132_);
lean_inc(v___x_134_);
v_val_137_ = lean_noption_get(v___x_134_);
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_acc_117_, v_val_136_);
switch(lean_obj_tag(v___x_144_))
{
case 0:
{
lean_object* v_index_145_; lean_object* v_size_146_; lean_object* v___x_147_; 
v_index_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_index_145_);
lean_dec_ref_known(v___x_144_, 3);
v_size_146_ = lean_ctor_get(v_acc_117_, 0);
lean_inc(v_size_146_);
v___x_147_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_117_, v_size_146_, v_index_145_, v_val_136_, v_val_137_);
lean_dec(v_index_145_);
v___y_120_ = v___x_147_;
goto v___jp_119_;
}
case 1:
{
lean_object* v_index_148_; 
v_index_148_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_index_148_);
lean_dec_ref_known(v___x_144_, 1);
v_i_139_ = v_index_148_;
goto v___jp_138_;
}
default: 
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_117_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_index_151_; 
v_index_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_index_151_);
lean_dec_ref_known(v___x_150_, 1);
v_i_139_ = v_index_151_;
goto v___jp_138_;
}
else
{
lean_dec(v_val_137_);
lean_dec(v_val_136_);
v___y_120_ = v_acc_117_;
goto v___jp_119_;
}
}
}
v___jp_138_:
{
lean_object* v_size_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_size_140_ = lean_ctor_get(v_acc_117_, 0);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_add(v_size_140_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_117_, v___x_142_, v_i_139_, v_val_136_, v_val_137_);
lean_dec(v_i_139_);
v___y_120_ = v___x_143_;
goto v___jp_119_;
}
}
}
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_i_118_, v___x_121_);
lean_dec(v_i_118_);
v_acc_117_ = v___y_120_;
v_i_118_ = v___x_122_;
goto _start;
}
v___jp_124_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_i_118_, v___x_125_);
lean_dec(v_i_118_);
v_i_118_ = v___x_126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_b_152_, lean_object* v_acc_153_, lean_object* v_i_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg(v_b_152_, v_acc_153_, v_i_154_);
lean_dec_ref(v_b_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg(lean_object* v_init_156_, lean_object* v_b_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg(v_b_157_, v_init_156_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg___boxed(lean_object* v_init_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg(v_init_160_, v_b_161_);
lean_dec_ref(v_b_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(lean_object* v_m_163_){
_start:
{
lean_object* v_keyArray_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_cellCount_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_target_171_; lean_object* v___x_172_; 
v_keyArray_164_ = lean_ctor_get(v_m_163_, 1);
v___x_165_ = lean_array_get_size(v_keyArray_164_);
v___x_166_ = lean_unsigned_to_nat(2u);
v_cellCount_167_ = lean_nat_mul(v___x_165_, v___x_166_);
v___x_168_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_167_);
v___x_169_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_167_);
v___x_170_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_167_);
v_target_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_171_, 0, v___x_168_);
lean_ctor_set(v_target_171_, 1, v___x_169_);
lean_ctor_set(v_target_171_, 2, v___x_170_);
v___x_172_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg(v_target_171_, v_m_163_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg___boxed(lean_object* v_m_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(v_m_173_);
lean_dec_ref(v_m_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(lean_object* v_m_175_, lean_object* v_query_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_175_, v_query_176_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_index_178_; lean_object* v_key_179_; lean_object* v_value_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
v_index_178_ = lean_ctor_get(v___x_177_, 0);
v_key_179_ = lean_ctor_get(v___x_177_, 1);
v_value_180_ = lean_ctor_get(v___x_177_, 2);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_177_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_value_180_);
lean_inc(v_key_179_);
lean_inc(v_index_178_);
lean_dec(v___x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_index_178_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_key_179_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_value_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v___x_177_);
v___x_188_ = lean_box(1);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg___boxed(lean_object* v_m_189_, lean_object* v_query_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_m_189_, v_query_190_);
lean_dec(v_query_190_);
lean_dec_ref(v_m_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_m_192_, v_a_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_value_195_; lean_object* v___x_196_; 
v_value_195_ = lean_ctor_get(v___x_194_, 2);
lean_inc(v_value_195_);
lean_dec_ref_known(v___x_194_, 3);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_value_195_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
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
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_372_; 
lean_inc_ref(v_paramNames_295_);
lean_inc_ref(v_map_294_);
lean_inc(v_nextIdx_293_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_373_ = lean_ctor_get(v_a_214_, 2);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_a_214_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_a_214_, 0);
lean_dec(v_unused_375_);
v___x_298_ = v_a_214_;
v_isShared_299_ = v_isSharedCheck_372_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_a_214_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_372_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___y_313_; lean_object* v_i_314_; lean_object* v___y_329_; lean_object* v_i_330_; lean_object* v___y_335_; lean_object* v___x_344_; 
v___x_300_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__1));
lean_inc(v_nextIdx_293_);
v___x_301_ = lean_name_append_index_after(v___x_300_, v_nextIdx_293_);
v___x_302_ = l_Lean_Level_param___override(v___x_301_);
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_nextIdx_293_, v___x_303_);
lean_dec(v_nextIdx_293_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_map_294_, v_a_292_);
switch(lean_obj_tag(v___x_344_))
{
case 0:
{
lean_object* v_index_345_; lean_object* v_size_346_; lean_object* v___x_347_; 
v_index_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_345_);
lean_dec_ref_known(v___x_344_, 3);
v_size_346_ = lean_ctor_get(v_map_294_, 0);
lean_inc(v_size_346_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_347_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_294_, v_size_346_, v_index_345_, v_a_292_, v___x_302_);
lean_dec(v_index_345_);
v___y_306_ = v___x_347_;
goto v___jp_305_;
}
case 1:
{
lean_object* v_index_348_; lean_object* v_size_349_; lean_object* v_keyArray_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_index_348_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_344_, 1);
v_size_349_ = lean_ctor_get(v_map_294_, 0);
v_keyArray_350_ = lean_ctor_get(v_map_294_, 1);
v___x_351_ = lean_nat_add(v_size_349_, v___x_303_);
v___x_352_ = lean_array_get_size(v_keyArray_350_);
v___x_353_ = lean_nat_dec_lt(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec(v___x_351_);
lean_dec(v_index_348_);
goto v___jp_318_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_354_ = lean_unsigned_to_nat(4u);
v___x_355_ = lean_nat_mul(v___x_351_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(3u);
v___x_357_ = lean_nat_mul(v___x_352_, v___x_356_);
v___x_358_ = lean_nat_dec_le(v___x_355_, v___x_357_);
lean_dec(v___x_357_);
lean_dec(v___x_355_);
if (v___x_358_ == 0)
{
lean_dec(v___x_351_);
lean_dec(v_index_348_);
goto v___jp_318_;
}
else
{
lean_object* v___x_359_; 
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_359_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_294_, v___x_351_, v_index_348_, v_a_292_, v___x_302_);
lean_dec(v_index_348_);
v___y_306_ = v___x_359_;
goto v___jp_305_;
}
}
}
default: 
{
lean_object* v_size_360_; lean_object* v_keyArray_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_size_360_ = lean_ctor_get(v_map_294_, 0);
v_keyArray_361_ = lean_ctor_get(v_map_294_, 1);
v___x_362_ = lean_nat_add(v_size_360_, v___x_303_);
v___x_363_ = lean_array_get_size(v_keyArray_361_);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v___x_362_);
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(v_map_294_);
lean_dec_ref(v_map_294_);
v___y_335_ = v___x_365_;
goto v___jp_334_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_366_ = lean_unsigned_to_nat(4u);
v___x_367_ = lean_nat_mul(v___x_362_, v___x_366_);
lean_dec(v___x_362_);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = lean_nat_mul(v___x_363_, v___x_368_);
v___x_370_ = lean_nat_dec_le(v___x_367_, v___x_369_);
lean_dec(v___x_369_);
lean_dec(v___x_367_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(v_map_294_);
lean_dec_ref(v_map_294_);
v___y_335_ = v___x_371_;
goto v___jp_334_;
}
else
{
v___y_335_ = v_map_294_;
goto v___jp_334_;
}
}
}
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = lean_array_push(v_paramNames_295_, v_a_292_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_307_);
lean_ctor_set(v___x_298_, 1, v___y_306_);
lean_ctor_set(v___x_298_, 0, v___x_304_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___y_306_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v___x_307_);
v___x_309_ = v_reuseFailAlloc_311_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_302_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
return v___x_310_;
}
}
v___jp_312_:
{
lean_object* v_size_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_size_315_ = lean_ctor_get(v___y_313_, 0);
v___x_316_ = lean_nat_add(v_size_315_, v___x_303_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_317_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_313_, v___x_316_, v_i_314_, v_a_292_, v___x_302_);
lean_dec(v_i_314_);
v___y_306_ = v___x_317_;
goto v___jp_305_;
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(v_map_294_);
lean_dec_ref(v_map_294_);
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v___x_319_, v_a_292_);
switch(lean_obj_tag(v___x_320_))
{
case 0:
{
lean_object* v_index_321_; lean_object* v_size_322_; lean_object* v___x_323_; 
v_index_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_index_321_);
lean_dec_ref_known(v___x_320_, 3);
v_size_322_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_size_322_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_323_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_319_, v_size_322_, v_index_321_, v_a_292_, v___x_302_);
lean_dec(v_index_321_);
v___y_306_ = v___x_323_;
goto v___jp_305_;
}
case 1:
{
lean_object* v_index_324_; 
v_index_324_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_index_324_);
lean_dec_ref_known(v___x_320_, 1);
v___y_313_ = v___x_319_;
v_i_314_ = v_index_324_;
goto v___jp_312_;
}
default: 
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_319_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_index_327_; 
v_index_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_index_327_);
lean_dec_ref_known(v___x_326_, 1);
v___y_313_ = v___x_319_;
v_i_314_ = v_index_327_;
goto v___jp_312_;
}
else
{
v___y_306_ = v___x_319_;
goto v___jp_305_;
}
}
}
}
v___jp_328_:
{
lean_object* v_size_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_size_331_ = lean_ctor_get(v___y_329_, 0);
v___x_332_ = lean_nat_add(v_size_331_, v___x_303_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_333_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_329_, v___x_332_, v_i_330_, v_a_292_, v___x_302_);
lean_dec(v_i_330_);
v___y_306_ = v___x_333_;
goto v___jp_305_;
}
v___jp_334_:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v___y_335_, v_a_292_);
switch(lean_obj_tag(v___x_336_))
{
case 0:
{
lean_object* v_index_337_; lean_object* v_size_338_; lean_object* v___x_339_; 
v_index_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_index_337_);
lean_dec_ref_known(v___x_336_, 3);
v_size_338_ = lean_ctor_get(v___y_335_, 0);
lean_inc(v_size_338_);
lean_inc(v___x_302_);
lean_inc(v_a_292_);
v___x_339_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_335_, v_size_338_, v_index_337_, v_a_292_, v___x_302_);
lean_dec(v_index_337_);
v___y_306_ = v___x_339_;
goto v___jp_305_;
}
case 1:
{
lean_object* v_index_340_; 
v_index_340_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_index_340_);
lean_dec_ref_known(v___x_336_, 1);
v___y_329_ = v___y_335_;
v_i_330_ = v_index_340_;
goto v___jp_328_;
}
default: 
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_335_, v___x_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_index_343_; 
v_index_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_index_343_);
lean_dec_ref_known(v___x_342_, 1);
v___y_329_ = v___y_335_;
v_i_330_ = v_index_343_;
goto v___jp_328_;
}
else
{
v___y_306_ = v___y_335_;
goto v___jp_305_;
}
}
}
}
}
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec(v_a_292_);
v_val_376_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v___x_296_, 1);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_val_376_);
lean_ctor_set(v___x_377_, 1, v_a_214_);
return v___x_377_;
}
}
default: 
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec_ref_known(v_u_213_, 1);
v___x_378_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5, &l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__5);
v___x_379_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3(v___x_378_, v_a_214_);
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(lean_object* v_00_u03b2_380_, lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___redArg(v_m_381_, v_a_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0___boxed(lean_object* v_00_u03b2_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0(v_00_u03b2_384_, v_m_385_, v_a_386_);
lean_dec(v_a_386_);
lean_dec_ref(v_m_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(lean_object* v_00_u03b2_388_, lean_object* v_m_389_, lean_object* v_query_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___redArg(v_m_389_, v_query_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1___boxed(lean_object* v_00_u03b2_392_, lean_object* v_m_393_, lean_object* v_query_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1(v_00_u03b2_392_, v_m_393_, v_query_394_);
lean_dec(v_query_394_);
lean_dec_ref(v_m_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(lean_object* v_00_u03b2_396_, lean_object* v_m_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___redArg(v_m_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2___boxed(lean_object* v_00_u03b2_399_, lean_object* v_m_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2(v_00_u03b2_399_, v_m_400_);
lean_dec_ref(v_m_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(lean_object* v_00_u03b2_402_, lean_object* v_m_403_, lean_object* v_query_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___redArg(v_m_403_, v_query_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_406_, lean_object* v_m_407_, lean_object* v_query_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__0_spec__0(v_00_u03b2_406_, v_m_407_, v_query_408_);
lean_dec(v_query_408_);
lean_dec_ref(v_m_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_query_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___redArg(v_m_411_, v_query_412_, v_x_413_, v_x_414_, v_x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2___boxed(lean_object* v_00_u03b2_418_, lean_object* v_m_419_, lean_object* v_query_420_, lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__1_spec__2(v_00_u03b2_418_, v_m_419_, v_query_420_, v_x_421_, v_x_422_, v_x_423_, v_x_424_);
lean_dec(v_query_420_);
lean_dec_ref(v_m_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4(lean_object* v_00_u03b2_426_, lean_object* v_init_427_, lean_object* v_b_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___redArg(v_init_427_, v_b_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4___boxed(lean_object* v_00_u03b2_430_, lean_object* v_init_431_, lean_object* v_b_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4(v_00_u03b2_430_, v_init_431_, v_b_432_);
lean_dec_ref(v_b_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_434_, lean_object* v_b_435_, lean_object* v_acc_436_, lean_object* v_i_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___redArg(v_b_435_, v_acc_436_, v_i_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_439_, lean_object* v_b_440_, lean_object* v_acc_441_, lean_object* v_i_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__2_spec__4_spec__6(v_00_u03b2_439_, v_b_440_, v_acc_441_, v_i_442_);
lean_dec_ref(v_b_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(lean_object* v_msg_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___f_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_5181__overap_468_; lean_object* v___x_469_; 
v___f_446_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__0));
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__1));
v___f_448_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__2));
v___f_449_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__3));
v___f_450_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__4));
v___f_451_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__5));
v___f_452_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normLevel_spec__3___closed__6));
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___f_446_);
lean_ctor_set(v___x_453_, 1, v___f_447_);
v___x_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___f_448_);
lean_ctor_set(v___x_454_, 2, v___f_449_);
lean_ctor_set(v___x_454_, 3, v___f_450_);
lean_ctor_set(v___x_454_, 4, v___f_451_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___f_452_);
lean_inc_ref_n(v___x_455_, 6);
v___f_456_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_456_, 0, v___x_455_);
v___f_457_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_457_, 0, v___x_455_);
v___f_458_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_458_, 0, v___x_455_);
v___f_459_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_459_, 0, v___x_455_);
v___x_460_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_460_, 0, lean_box(0));
lean_closure_set(v___x_460_, 1, lean_box(0));
lean_closure_set(v___x_460_, 2, v___x_455_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___f_456_);
v___x_462_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_462_, 0, lean_box(0));
lean_closure_set(v___x_462_, 1, lean_box(0));
lean_closure_set(v___x_462_, 2, v___x_455_);
v___x_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_ctor_set(v___x_463_, 2, v___f_457_);
lean_ctor_set(v___x_463_, 3, v___f_458_);
lean_ctor_set(v___x_463_, 4, v___f_459_);
v___x_464_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_464_, 0, lean_box(0));
lean_closure_set(v___x_464_, 1, lean_box(0));
lean_closure_set(v___x_464_, 2, v___x_455_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_instInhabitedExpr;
v___x_467_ = l_instInhabitedOfMonad___redArg(v___x_465_, v___x_466_);
v___x_5181__overap_468_ = lean_panic_fn_borrowed(v___x_467_, v_msg_444_);
lean_dec(v___x_467_);
v___x_469_ = lean_apply_1(v___x_5181__overap_468_, v___y_445_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v___y_472_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = l_List_reverse___redArg(v_x_471_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___y_472_);
return v___x_474_;
}
else
{
lean_object* v_head_475_; lean_object* v_tail_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_487_; 
v_head_475_ = lean_ctor_get(v_x_470_, 0);
v_tail_476_ = lean_ctor_get(v_x_470_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_487_ == 0)
{
v___x_478_ = v_x_470_;
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_tail_476_);
lean_inc(v_head_475_);
lean_dec(v_x_470_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_487_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; 
v___x_480_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_head_475_, v___y_472_);
v_fst_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_fst_481_);
v_snd_482_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_snd_482_);
lean_dec_ref(v___x_480_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_x_471_);
lean_ctor_set(v___x_478_, 0, v_fst_481_);
v___x_484_ = v___x_478_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_fst_481_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_x_471_);
v___x_484_ = v_reuseFailAlloc_486_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v_x_470_ = v_tail_476_;
v_x_471_ = v___x_484_;
v___y_472_ = v_snd_482_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__4));
v___x_490_ = lean_unsigned_to_nat(26u);
v___x_491_ = lean_unsigned_to_nat(79u);
v___x_492_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__0));
v___x_493_ = ((lean_object*)(l_Lean_Compiler_LCNF_NormLevelParam_normLevel___closed__2));
v___x_494_ = l_mkPanicMessageWithDecl(v___x_493_, v___x_492_, v___x_491_, v___x_490_, v___x_489_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_NormLevelParam_normExpr(lean_object* v_e_495_, lean_object* v_a_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_Expr_hasLevelParam(v_e_495_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_e_495_);
lean_ctor_set(v___x_498_, 1, v_a_496_);
return v___x_498_;
}
else
{
switch(lean_obj_tag(v_e_495_))
{
case 4:
{
lean_object* v_declName_499_; lean_object* v_us_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_fst_503_; lean_object* v_snd_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
v_declName_499_ = lean_ctor_get(v_e_495_, 0);
v_us_500_ = lean_ctor_get(v_e_495_, 1);
v___x_501_ = lean_box(0);
lean_inc(v_us_500_);
v___x_502_ = l_List_mapM_loop___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__0(v_us_500_, v___x_501_, v_a_496_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
v_snd_504_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_516_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_snd_504_);
lean_inc(v_fst_503_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = l_ptrEqList___redArg(v_us_500_, v_fst_503_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_inc(v_declName_499_);
lean_dec_ref_known(v_e_495_, 2);
v___x_509_ = l_Lean_Expr_const___override(v_declName_499_, v_fst_503_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_snd_504_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_fst_503_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v_e_495_);
v___x_514_ = v___x_506_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_snd_504_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
case 3:
{
lean_object* v_u_517_; lean_object* v___x_518_; lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_534_; 
v_u_517_ = lean_ctor_get(v_e_495_, 0);
lean_inc(v_u_517_);
v___x_518_ = l_Lean_Compiler_LCNF_NormLevelParam_normLevel(v_u_517_, v_a_496_);
v_fst_519_ = lean_ctor_get(v___x_518_, 0);
v_snd_520_ = lean_ctor_get(v___x_518_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_534_ == 0)
{
v___x_522_ = v___x_518_;
v_isShared_523_ = v_isSharedCheck_534_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v___x_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_534_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_ptr_addr(v_u_517_);
v___x_525_ = lean_ptr_addr(v_fst_519_);
v___x_526_ = lean_usize_dec_eq(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec_ref_known(v_e_495_, 1);
v___x_527_ = l_Lean_Expr_sort___override(v_fst_519_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_527_);
v___x_529_ = v___x_522_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_520_);
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
lean_dec(v_fst_519_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_e_495_);
v___x_532_ = v___x_522_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_snd_520_);
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
case 5:
{
lean_object* v_fn_535_; lean_object* v_arg_536_; lean_object* v___x_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_540_; lean_object* v_fst_541_; lean_object* v_snd_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_561_; 
v_fn_535_ = lean_ctor_get(v_e_495_, 0);
v_arg_536_ = lean_ctor_get(v_e_495_, 1);
lean_inc_ref(v_fn_535_);
v___x_537_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_fn_535_, v_a_496_);
v_fst_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_fst_538_);
v_snd_539_ = lean_ctor_get(v___x_537_, 1);
lean_inc(v_snd_539_);
lean_dec_ref(v___x_537_);
lean_inc_ref(v_arg_536_);
v___x_540_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_arg_536_, v_snd_539_);
v_fst_541_ = lean_ctor_get(v___x_540_, 0);
v_snd_542_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_561_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_561_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snd_542_);
lean_inc(v_fst_541_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_561_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v___y_547_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_ptr_addr(v_fn_535_);
v___x_556_ = lean_ptr_addr(v_fst_538_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
v___y_547_ = v___x_557_;
goto v___jp_546_;
}
else
{
size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = lean_ptr_addr(v_arg_536_);
v___x_559_ = lean_ptr_addr(v_fst_541_);
v___x_560_ = lean_usize_dec_eq(v___x_558_, v___x_559_);
v___y_547_ = v___x_560_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec_ref_known(v_e_495_, 2);
v___x_548_ = l_Lean_Expr_app___override(v_fst_538_, v_fst_541_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v___x_548_);
v___x_550_ = v___x_544_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_snd_542_);
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
lean_object* v___x_553_; 
lean_dec(v_fst_541_);
lean_dec(v_fst_538_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 0, v_e_495_);
v___x_553_ = v___x_544_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_snd_542_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
case 8:
{
lean_object* v_declName_562_; lean_object* v_type_563_; lean_object* v_value_564_; lean_object* v_body_565_; uint8_t v_nondep_566_; lean_object* v___x_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_601_; 
v_declName_562_ = lean_ctor_get(v_e_495_, 0);
v_type_563_ = lean_ctor_get(v_e_495_, 1);
v_value_564_ = lean_ctor_get(v_e_495_, 2);
v_body_565_ = lean_ctor_get(v_e_495_, 3);
v_nondep_566_ = lean_ctor_get_uint8(v_e_495_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_563_);
v___x_567_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_type_563_, v_a_496_);
v_fst_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_fst_568_);
v_snd_569_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_snd_569_);
lean_dec_ref(v___x_567_);
lean_inc_ref(v_value_564_);
v___x_570_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_value_564_, v_snd_569_);
v_fst_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_570_);
lean_inc_ref(v_body_565_);
v___x_573_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_565_, v_snd_572_);
v_fst_574_ = lean_ctor_get(v___x_573_, 0);
v_snd_575_ = lean_ctor_get(v___x_573_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_601_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_601_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_601_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___y_580_; size_t v___x_595_; size_t v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_ptr_addr(v_type_563_);
v___x_596_ = lean_ptr_addr(v_fst_568_);
v___x_597_ = lean_usize_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_580_ = v___x_597_;
goto v___jp_579_;
}
else
{
size_t v___x_598_; size_t v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_ptr_addr(v_value_564_);
v___x_599_ = lean_ptr_addr(v_fst_571_);
v___x_600_ = lean_usize_dec_eq(v___x_598_, v___x_599_);
v___y_580_ = v___x_600_;
goto v___jp_579_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc(v_declName_562_);
lean_dec_ref_known(v_e_495_, 4);
v___x_581_ = l_Lean_Expr_letE___override(v_declName_562_, v_fst_568_, v_fst_571_, v_fst_574_, v_nondep_566_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_581_);
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_snd_575_);
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
size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_ptr_addr(v_body_565_);
v___x_586_ = lean_ptr_addr(v_fst_574_);
v___x_587_ = lean_usize_dec_eq(v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_590_; 
lean_inc(v_declName_562_);
lean_dec_ref_known(v_e_495_, 4);
v___x_588_ = l_Lean_Expr_letE___override(v_declName_562_, v_fst_568_, v_fst_571_, v_fst_574_, v_nondep_566_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_588_);
v___x_590_ = v___x_577_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_snd_575_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v_fst_574_);
lean_dec(v_fst_571_);
lean_dec(v_fst_568_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_e_495_);
v___x_593_ = v___x_577_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_575_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_602_; lean_object* v_binderType_603_; lean_object* v_body_604_; uint8_t v_binderInfo_605_; lean_object* v___x_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_635_; 
v_binderName_602_ = lean_ctor_get(v_e_495_, 0);
v_binderType_603_ = lean_ctor_get(v_e_495_, 1);
v_body_604_ = lean_ctor_get(v_e_495_, 2);
v_binderInfo_605_ = lean_ctor_get_uint8(v_e_495_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_603_);
v___x_606_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_603_, v_a_496_);
v_fst_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_fst_607_);
v_snd_608_ = lean_ctor_get(v___x_606_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___x_606_);
lean_inc_ref(v_body_604_);
v___x_609_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_604_, v_snd_608_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_635_ == 0)
{
v___x_613_ = v___x_609_;
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v___x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_635_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___y_616_; size_t v___x_629_; size_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_ptr_addr(v_binderType_603_);
v___x_630_ = lean_ptr_addr(v_fst_607_);
v___x_631_ = lean_usize_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_616_ = v___x_631_;
goto v___jp_615_;
}
else
{
size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_ptr_addr(v_body_604_);
v___x_633_ = lean_ptr_addr(v_fst_610_);
v___x_634_ = lean_usize_dec_eq(v___x_632_, v___x_633_);
v___y_616_ = v___x_634_;
goto v___jp_615_;
}
v___jp_615_:
{
if (v___y_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_619_; 
lean_inc(v_binderName_602_);
lean_dec_ref_known(v_e_495_, 3);
v___x_617_ = l_Lean_Expr_forallE___override(v_binderName_602_, v_fst_607_, v_fst_610_, v_binderInfo_605_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_snd_611_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_605_, v_binderInfo_605_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_624_; 
lean_inc(v_binderName_602_);
lean_dec_ref_known(v_e_495_, 3);
v___x_622_ = l_Lean_Expr_forallE___override(v_binderName_602_, v_fst_607_, v_fst_610_, v_binderInfo_605_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_622_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_snd_611_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; 
lean_dec(v_fst_610_);
lean_dec(v_fst_607_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_e_495_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_snd_611_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_636_; lean_object* v_binderType_637_; lean_object* v_body_638_; uint8_t v_binderInfo_639_; lean_object* v___x_640_; lean_object* v_fst_641_; lean_object* v_snd_642_; lean_object* v___x_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_669_; 
v_binderName_636_ = lean_ctor_get(v_e_495_, 0);
v_binderType_637_ = lean_ctor_get(v_e_495_, 1);
v_body_638_ = lean_ctor_get(v_e_495_, 2);
v_binderInfo_639_ = lean_ctor_get_uint8(v_e_495_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_637_);
v___x_640_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_binderType_637_, v_a_496_);
v_fst_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_fst_641_);
v_snd_642_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_snd_642_);
lean_dec_ref(v___x_640_);
lean_inc_ref(v_body_638_);
v___x_643_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_body_638_, v_snd_642_);
v_fst_644_ = lean_ctor_get(v___x_643_, 0);
v_snd_645_ = lean_ctor_get(v___x_643_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_669_ == 0)
{
v___x_647_ = v___x_643_;
v_isShared_648_ = v_isSharedCheck_669_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_snd_645_);
lean_inc(v_fst_644_);
lean_dec(v___x_643_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_669_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___y_650_; size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_ptr_addr(v_binderType_637_);
v___x_664_ = lean_ptr_addr(v_fst_641_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
v___y_650_ = v___x_665_;
goto v___jp_649_;
}
else
{
size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_ptr_addr(v_body_638_);
v___x_667_ = lean_ptr_addr(v_fst_644_);
v___x_668_ = lean_usize_dec_eq(v___x_666_, v___x_667_);
v___y_650_ = v___x_668_;
goto v___jp_649_;
}
v___jp_649_:
{
if (v___y_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_653_; 
lean_inc(v_binderName_636_);
lean_dec_ref_known(v_e_495_, 3);
v___x_651_ = l_Lean_Expr_lam___override(v_binderName_636_, v_fst_641_, v_fst_644_, v_binderInfo_639_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_651_);
v___x_653_ = v___x_647_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_645_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
uint8_t v___x_655_; 
v___x_655_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_639_, v_binderInfo_639_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v_binderName_636_);
lean_dec_ref_known(v_e_495_, 3);
v___x_656_ = l_Lean_Expr_lam___override(v_binderName_636_, v_fst_641_, v_fst_644_, v_binderInfo_639_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_656_);
v___x_658_ = v___x_647_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_snd_645_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
lean_object* v___x_661_; 
lean_dec(v_fst_644_);
lean_dec(v_fst_641_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v_e_495_);
v___x_661_ = v___x_647_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_snd_645_);
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
}
}
case 10:
{
lean_object* v_data_670_; lean_object* v_expr_671_; lean_object* v___x_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_688_; 
v_data_670_ = lean_ctor_get(v_e_495_, 0);
v_expr_671_ = lean_ctor_get(v_e_495_, 1);
lean_inc_ref(v_expr_671_);
v___x_672_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_expr_671_, v_a_496_);
v_fst_673_ = lean_ctor_get(v___x_672_, 0);
v_snd_674_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_688_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_688_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snd_674_);
lean_inc(v_fst_673_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_688_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
size_t v___x_678_; size_t v___x_679_; uint8_t v___x_680_; 
v___x_678_ = lean_ptr_addr(v_expr_671_);
v___x_679_ = lean_ptr_addr(v_fst_673_);
v___x_680_ = lean_usize_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc(v_data_670_);
lean_dec_ref_known(v_e_495_, 2);
v___x_681_ = l_Lean_Expr_mdata___override(v_data_670_, v_fst_673_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_681_);
v___x_683_ = v___x_676_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_snd_674_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
lean_object* v___x_686_; 
lean_dec(v_fst_673_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_e_495_);
v___x_686_ = v___x_676_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_snd_674_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
case 11:
{
lean_object* v_typeName_689_; lean_object* v_idx_690_; lean_object* v_struct_691_; lean_object* v___x_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_708_; 
v_typeName_689_ = lean_ctor_get(v_e_495_, 0);
v_idx_690_ = lean_ctor_get(v_e_495_, 1);
v_struct_691_ = lean_ctor_get(v_e_495_, 2);
lean_inc_ref(v_struct_691_);
v___x_692_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_struct_691_, v_a_496_);
v_fst_693_ = lean_ctor_get(v___x_692_, 0);
v_snd_694_ = lean_ctor_get(v___x_692_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_696_ = v___x_692_;
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v___x_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_ptr_addr(v_struct_691_);
v___x_699_ = lean_ptr_addr(v_fst_693_);
v___x_700_ = lean_usize_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_703_; 
lean_inc(v_idx_690_);
lean_inc(v_typeName_689_);
lean_dec_ref_known(v_e_495_, 3);
v___x_701_ = l_Lean_Expr_proj___override(v_typeName_689_, v_idx_690_, v_fst_693_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_701_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_694_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_fst_693_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_e_495_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_e_495_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_snd_694_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
case 2:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref_known(v_e_495_, 1);
v___x_709_ = lean_obj_once(&l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1, &l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1_once, _init_l_Lean_Compiler_LCNF_NormLevelParam_normExpr___closed__1);
v___x_710_ = l_panic___at___00Lean_Compiler_LCNF_NormLevelParam_normExpr_spec__1(v___x_709_, v_a_496_);
return v___x_710_;
}
default: 
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_e_495_);
lean_ctor_set(v___x_711_, 1, v_a_496_);
return v___x_711_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0(void){
_start:
{
lean_object* v_cellCount_712_; lean_object* v___x_713_; 
v_cellCount_712_ = lean_unsigned_to_nat(16u);
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1(void){
_start:
{
lean_object* v_cellCount_714_; lean_object* v___x_715_; 
v_cellCount_714_ = lean_unsigned_to_nat(16u);
v___x_715_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__2(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__1, &l_Lean_Compiler_LCNF_normLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__1);
v___x_717_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__0, &l_Lean_Compiler_LCNF_normLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__0);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_717_);
lean_ctor_set(v___x_719_, 2, v___x_716_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normLevelParams___closed__4(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__3));
v___x_723_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__2, &l_Lean_Compiler_LCNF_normLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__2);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_722_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object* v_e_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_snd_729_; lean_object* v_fst_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_739_; 
v___x_727_ = lean_obj_once(&l_Lean_Compiler_LCNF_normLevelParams___closed__4, &l_Lean_Compiler_LCNF_normLevelParams___closed__4_once, _init_l_Lean_Compiler_LCNF_normLevelParams___closed__4);
v___x_728_ = l_Lean_Compiler_LCNF_NormLevelParam_normExpr(v_e_726_, v___x_727_);
v_snd_729_ = lean_ctor_get(v___x_728_, 1);
v_fst_730_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_739_ == 0)
{
v___x_732_ = v___x_728_;
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_730_);
lean_dec(v___x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_paramNames_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v_paramNames_734_ = lean_ctor_get(v_snd_729_, 2);
lean_inc_ref(v_paramNames_734_);
lean_dec(v_snd_729_);
v___x_735_ = lean_array_to_list(v_paramNames_734_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_fst_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitType(lean_object* v_type_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_CollectLevelParams_visitExpr(v_type_740_, v_a_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(lean_object* v_arg_743_, lean_object* v_a_744_){
_start:
{
if (lean_obj_tag(v_arg_743_) == 2)
{
lean_object* v_expr_745_; lean_object* v___x_746_; 
v_expr_745_ = lean_ctor_get(v_arg_743_, 0);
lean_inc_ref(v_expr_745_);
lean_dec_ref_known(v_arg_743_, 1);
v___x_746_ = l_Lean_CollectLevelParams_visitExpr(v_expr_745_, v_a_744_);
return v___x_746_;
}
else
{
lean_dec(v_arg_743_);
return v_a_744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(lean_object* v_as_747_, size_t v_i_748_, size_t v_stop_749_, lean_object* v_b_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_eq(v_i_748_, v_stop_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; 
v___x_752_ = lean_array_uget_borrowed(v_as_747_, v_i_748_);
lean_inc(v___x_752_);
v___x_753_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArg(v___x_752_, v_b_750_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0___boxed(lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_stop_759_, lean_object* v_b_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_759_);
lean_dec(v_stop_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_as_757_, v_i_boxed_761_, v_stop_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(lean_object* v_args_764_, lean_object* v_s_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_array_get_size(v_args_764_);
v___x_768_ = lean_nat_dec_lt(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
return v_s_765_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_le(v___x_767_, v___x_767_);
if (v___x_769_ == 0)
{
if (v___x_768_ == 0)
{
return v_s_765_;
}
else
{
size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((size_t)0ULL);
v___x_771_ = lean_usize_of_nat(v___x_767_);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_764_, v___x_770_, v___x_771_, v_s_765_);
return v___x_772_;
}
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_773_ = ((size_t)0ULL);
v___x_774_ = lean_usize_of_nat(v___x_767_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitArgs_spec__0(v_args_764_, v___x_773_, v___x_774_, v_s_765_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs___boxed(lean_object* v_args_776_, lean_object* v_s_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_776_, v_s_777_);
lean_dec_ref(v_args_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(lean_object* v_e_779_, lean_object* v_a_780_){
_start:
{
switch(lean_obj_tag(v_e_779_))
{
case 3:
{
lean_object* v_us_781_; lean_object* v_args_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_us_781_ = lean_ctor_get(v_e_779_, 1);
lean_inc(v_us_781_);
v_args_782_ = lean_ctor_get(v_e_779_, 2);
lean_inc_ref(v_args_782_);
lean_dec_ref_known(v_e_779_, 3);
v___x_783_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_782_, v_a_780_);
lean_dec_ref(v_args_782_);
v___x_784_ = l_Lean_CollectLevelParams_visitLevels(v_us_781_, v___x_783_);
return v___x_784_;
}
case 4:
{
lean_object* v_args_785_; lean_object* v___x_786_; 
v_args_785_ = lean_ctor_get(v_e_779_, 1);
lean_inc_ref(v_args_785_);
lean_dec_ref_known(v_e_779_, 2);
v___x_786_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_785_, v_a_780_);
lean_dec_ref(v_args_785_);
return v___x_786_;
}
default: 
{
lean_dec(v_e_779_);
return v_a_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(lean_object* v_p_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_type_789_; lean_object* v___x_790_; 
v_type_789_ = lean_ctor_get(v_p_787_, 2);
lean_inc_ref(v_type_789_);
lean_dec_ref(v_p_787_);
v___x_790_ = l_Lean_CollectLevelParams_visitExpr(v_type_789_, v_a_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(lean_object* v_as_791_, size_t v_i_792_, size_t v_stop_793_, lean_object* v_b_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = lean_usize_dec_eq(v_i_792_, v_stop_793_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; size_t v___x_798_; size_t v___x_799_; 
v___x_796_ = lean_array_uget_borrowed(v_as_791_, v_i_792_);
lean_inc(v___x_796_);
v___x_797_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParam(v___x_796_, v_b_794_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_792_, v___x_798_);
v_i_792_ = v___x_799_;
v_b_794_ = v___x_797_;
goto _start;
}
else
{
return v_b_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0___boxed(lean_object* v_as_801_, lean_object* v_i_802_, lean_object* v_stop_803_, lean_object* v_b_804_){
_start:
{
size_t v_i_boxed_805_; size_t v_stop_boxed_806_; lean_object* v_res_807_; 
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_stop_boxed_806_ = lean_unbox_usize(v_stop_803_);
lean_dec(v_stop_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_as_801_, v_i_boxed_805_, v_stop_boxed_806_, v_b_804_);
lean_dec_ref(v_as_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(lean_object* v_ps_808_, lean_object* v_s_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_ps_808_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
return v_s_809_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = lean_nat_dec_le(v___x_811_, v___x_811_);
if (v___x_813_ == 0)
{
if (v___x_812_ == 0)
{
return v_s_809_;
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_811_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_808_, v___x_814_, v___x_815_, v_s_809_);
return v___x_816_;
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_811_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitParams_spec__0(v_ps_808_, v___x_817_, v___x_818_, v_s_809_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitParams___boxed(lean_object* v_ps_820_, lean_object* v_s_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_ps_820_, v_s_821_);
lean_dec_ref(v_ps_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(lean_object* v_as_823_, size_t v_i_824_, size_t v_stop_825_, lean_object* v_b_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = lean_usize_dec_eq(v_i_824_, v_stop_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; size_t v___x_830_; size_t v___x_831_; 
v___x_828_ = lean_array_uget_borrowed(v_as_823_, v_i_824_);
lean_inc(v___x_828_);
v___x_829_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(v___x_828_, v_b_826_);
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_824_, v___x_830_);
v_i_824_ = v___x_831_;
v_b_826_ = v___x_829_;
goto _start;
}
else
{
return v_b_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(lean_object* v_alts_833_, lean_object* v_s_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_array_get_size(v_alts_833_);
v___x_837_ = lean_nat_dec_lt(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
return v_s_834_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_le(v___x_836_, v___x_836_);
if (v___x_838_ == 0)
{
if (v___x_837_ == 0)
{
return v_s_834_;
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_836_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_833_, v___x_839_, v___x_840_, v_s_834_);
return v___x_841_;
}
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_836_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_alts_833_, v___x_842_, v___x_843_, v_s_834_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(lean_object* v_x_845_, lean_object* v_a_846_){
_start:
{
switch(lean_obj_tag(v_x_845_))
{
case 0:
{
lean_object* v_decl_847_; lean_object* v_k_848_; lean_object* v_type_849_; lean_object* v_value_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_decl_847_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_decl_847_);
v_k_848_ = lean_ctor_get(v_x_845_, 1);
lean_inc_ref(v_k_848_);
lean_dec_ref_known(v_x_845_, 2);
v_type_849_ = lean_ctor_get(v_decl_847_, 2);
lean_inc_ref(v_type_849_);
v_value_850_ = lean_ctor_get(v_decl_847_, 3);
lean_inc(v_value_850_);
lean_dec_ref(v_decl_847_);
v___x_851_ = l_Lean_CollectLevelParams_visitExpr(v_type_849_, v_a_846_);
v___x_852_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitLetValue(v_value_850_, v___x_851_);
v_x_845_ = v_k_848_;
v_a_846_ = v___x_852_;
goto _start;
}
case 3:
{
lean_object* v_args_854_; lean_object* v___x_855_; 
v_args_854_ = lean_ctor_get(v_x_845_, 1);
lean_inc_ref(v_args_854_);
lean_dec_ref_known(v_x_845_, 2);
v___x_855_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitArgs(v_args_854_, v_a_846_);
lean_dec_ref(v_args_854_);
return v___x_855_;
}
case 4:
{
lean_object* v_cases_856_; lean_object* v_resultType_857_; lean_object* v_alts_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_cases_856_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_cases_856_);
lean_dec_ref_known(v_x_845_, 1);
v_resultType_857_ = lean_ctor_get(v_cases_856_, 1);
lean_inc_ref(v_resultType_857_);
v_alts_858_ = lean_ctor_get(v_cases_856_, 3);
lean_inc_ref(v_alts_858_);
lean_dec_ref(v_cases_856_);
v___x_859_ = l_Lean_CollectLevelParams_visitExpr(v_resultType_857_, v_a_846_);
v___x_860_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_858_, v___x_859_);
lean_dec_ref(v_alts_858_);
return v___x_860_;
}
case 5:
{
lean_dec_ref_known(v_x_845_, 1);
return v_a_846_;
}
case 6:
{
lean_object* v_type_861_; lean_object* v___x_862_; 
v_type_861_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_type_861_);
lean_dec_ref_known(v_x_845_, 1);
v___x_862_ = l_Lean_CollectLevelParams_visitExpr(v_type_861_, v_a_846_);
return v___x_862_;
}
default: 
{
lean_object* v_decl_863_; lean_object* v_k_864_; lean_object* v_params_865_; lean_object* v_type_866_; lean_object* v_value_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_decl_863_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_decl_863_);
v_k_864_ = lean_ctor_get(v_x_845_, 1);
lean_inc_ref(v_k_864_);
lean_dec_ref(v_x_845_);
v_params_865_ = lean_ctor_get(v_decl_863_, 2);
lean_inc_ref(v_params_865_);
v_type_866_ = lean_ctor_get(v_decl_863_, 3);
lean_inc_ref(v_type_866_);
v_value_867_ = lean_ctor_get(v_decl_863_, 4);
lean_inc_ref(v_value_867_);
lean_dec_ref(v_decl_863_);
v___x_868_ = l_Lean_CollectLevelParams_visitExpr(v_type_866_, v_a_846_);
v___x_869_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_865_, v___x_868_);
lean_dec_ref(v_params_865_);
v___x_870_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_value_867_, v___x_869_);
v_x_845_ = v_k_864_;
v_a_846_ = v___x_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlt(lean_object* v_alt_872_, lean_object* v_a_873_){
_start:
{
if (lean_obj_tag(v_alt_872_) == 0)
{
lean_object* v_params_874_; lean_object* v_code_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_params_874_ = lean_ctor_get(v_alt_872_, 1);
lean_inc_ref(v_params_874_);
v_code_875_ = lean_ctor_get(v_alt_872_, 2);
lean_inc_ref(v_code_875_);
lean_dec_ref_known(v_alt_872_, 3);
v___x_876_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_874_, v_a_873_);
lean_dec_ref(v_params_874_);
v___x_877_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_875_, v___x_876_);
return v___x_877_;
}
else
{
lean_object* v_code_878_; lean_object* v___x_879_; 
v_code_878_ = lean_ctor_get(v_alt_872_, 0);
lean_inc_ref(v_code_878_);
lean_dec_ref_known(v_alt_872_, 1);
v___x_879_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_878_, v_a_873_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2___boxed(lean_object* v_as_880_, lean_object* v_i_881_, lean_object* v_stop_882_, lean_object* v_b_883_){
_start:
{
size_t v_i_boxed_884_; size_t v_stop_boxed_885_; lean_object* v_res_886_; 
v_i_boxed_884_ = lean_unbox_usize(v_i_881_);
lean_dec(v_i_881_);
v_stop_boxed_885_ = lean_unbox_usize(v_stop_882_);
lean_dec(v_stop_882_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_CollectLevelParams_visitAlts_spec__2(v_as_880_, v_i_boxed_884_, v_stop_boxed_885_, v_b_883_);
lean_dec_ref(v_as_880_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts___boxed(lean_object* v_alts_887_, lean_object* v_s_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitAlts(v_alts_887_, v_s_888_);
lean_dec_ref(v_alts_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(lean_object* v_x_890_, lean_object* v_a_891_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
lean_object* v_code_892_; lean_object* v___x_893_; 
v_code_892_ = lean_ctor_get(v_x_890_, 0);
lean_inc_ref(v_code_892_);
lean_dec_ref_known(v_x_890_, 1);
v___x_893_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitCode(v_code_892_, v_a_891_);
return v___x_893_;
}
else
{
lean_dec_ref_known(v_x_890_, 1);
return v_a_891_;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0(void){
_start:
{
lean_object* v_cellCount_894_; lean_object* v___x_895_; 
v_cellCount_894_ = lean_unsigned_to_nat(16u);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1(void){
_start:
{
lean_object* v_cellCount_896_; lean_object* v___x_897_; 
v_cellCount_896_ = lean_unsigned_to_nat(16u);
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_896_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__1);
v___x_899_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__0);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_898_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = ((lean_object*)(l_Lean_Compiler_LCNF_normLevelParams___closed__3));
v___x_903_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__2);
v___x_904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
lean_ctor_set(v___x_904_, 2, v___x_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object* v_decl_905_){
_start:
{
lean_object* v_toSignature_906_; lean_object* v_value_907_; uint8_t v_recursive_908_; lean_object* v_inlineAttr_x3f_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_934_; 
v_toSignature_906_ = lean_ctor_get(v_decl_905_, 0);
v_value_907_ = lean_ctor_get(v_decl_905_, 1);
v_recursive_908_ = lean_ctor_get_uint8(v_decl_905_, sizeof(void*)*3);
v_inlineAttr_x3f_909_ = lean_ctor_get(v_decl_905_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_decl_905_);
if (v_isSharedCheck_934_ == 0)
{
v___x_911_ = v_decl_905_;
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_inlineAttr_x3f_909_);
lean_inc(v_value_907_);
lean_inc(v_toSignature_906_);
lean_dec(v_decl_905_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_name_913_; lean_object* v_type_914_; lean_object* v_params_915_; uint8_t v_safe_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_932_; 
v_name_913_ = lean_ctor_get(v_toSignature_906_, 0);
v_type_914_ = lean_ctor_get(v_toSignature_906_, 2);
v_params_915_ = lean_ctor_get(v_toSignature_906_, 3);
v_safe_916_ = lean_ctor_get_uint8(v_toSignature_906_, sizeof(void*)*4);
v_isSharedCheck_932_ = !lean_is_exclusive(v_toSignature_906_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_toSignature_906_, 1);
lean_dec(v_unused_933_);
v___x_918_ = v_toSignature_906_;
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_params_915_);
lean_inc(v_type_914_);
lean_inc(v_name_913_);
lean_dec(v_toSignature_906_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_params_924_; lean_object* v_levelParams_925_; lean_object* v___x_927_; 
v___x_920_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3, &l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3_once, _init_l_Lean_Compiler_LCNF_Decl_setLevelParams___closed__3);
lean_inc_ref(v_type_914_);
v___x_921_ = l_Lean_CollectLevelParams_visitExpr(v_type_914_, v___x_920_);
v___x_922_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitParams(v_params_915_, v___x_921_);
lean_inc_ref(v_value_907_);
v___x_923_ = l_Lean_Compiler_LCNF_CollectLevelParams_visitDeclValue(v_value_907_, v___x_922_);
v_params_924_ = lean_ctor_get(v___x_923_, 2);
lean_inc_ref(v_params_924_);
lean_dec_ref(v___x_923_);
v_levelParams_925_ = lean_array_to_list(v_params_924_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_levelParams_925_);
v___x_927_ = v___x_918_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_name_913_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_levelParams_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_type_914_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_params_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*4, v_safe_916_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_927_);
v___x_929_ = v___x_911_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_value_907_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_inlineAttr_x3f_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, sizeof(void*)*3, v_recursive_908_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
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
