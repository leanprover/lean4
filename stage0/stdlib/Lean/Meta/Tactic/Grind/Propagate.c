// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Propagate
// Imports: import Init.Grind import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Ext import Lean.Meta.Tactic.Grind.Diseq public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqBoolTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqBoolFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerParent___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Solvers_propagateDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "and_eq_of_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 108, 85, 20, 119, 45, 62, 65)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndUp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__6;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "and_eq_of_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(42, 144, 170, 255, 103, 245, 81, 212)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "and_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(251, 27, 120, 129, 126, 49, 187, 13)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndUp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__12;
static const lean_string_object l_Lean_Meta_Grind_propagateAndUp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "and_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndUp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(230, 88, 90, 113, 195, 40, 138, 59)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndUp___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndUp___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateAndDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "eq_true_of_and_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 148, 180, 55, 174, 141, 160, 204)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateAndDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "eq_true_of_and_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateAndDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 133, 90, 124, 15, 221, 47, 193)}};
static const lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateAndDown___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateAndDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "or_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 166, 32, 31, 112, 92, 57, 243)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "or_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(32, 77, 158, 9, 2, 239, 232, 91)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "or_eq_of_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(249, 16, 179, 228, 207, 170, 243, 86)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__10;
static const lean_string_object l_Lean_Meta_Grind_propagateOrUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "or_eq_of_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrUp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(36, 196, 166, 85, 112, 30, 44, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrUp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrUp___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateOrDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "eq_false_of_or_eq_false_left"};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 204, 80, 248, 17, 222, 207, 37)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateOrDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "eq_false_of_or_eq_false_right"};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateOrDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(4, 189, 1, 60, 23, 208, 33, 127)}};
static const lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateOrDown___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateOrDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "false_of_not_eq_self"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 254, 86, 23, 186, 196, 13, 177)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateNotUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not_eq_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(209, 136, 252, 63, 150, 209, 33, 198)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateNotUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateNotUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "not_eq_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(197, 159, 169, 125, 202, 111, 60, 105)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateNotUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateNotUp___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateNotDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 178, 136, 115, 199, 101, 23, 5)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateNotDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateNotDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_true_of_not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateNotDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(164, 226, 232, 29, 193, 151, 102, 169)}};
static const lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateNotDown___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateNotDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_false_of_not_eq_true'"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 183, 221, 210, 33, 132, 178, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolDiseq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_true_of_not_eq_false'"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 231, 120, 149, 98, 142, 70, 153)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolDiseq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_false_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(152, 226, 34, 210, 0, 5, 65, 76)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateEqUp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__6;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "eq_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(109, 195, 236, 103, 135, 232, 42, 67)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateEqUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "eq_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(107, 111, 216, 64, 67, 213, 235, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateEqUp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LawfulBEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 131, 20, 143, 70, 69, 65, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "beq_eq_false_of_diseq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(172, 208, 214, 246, 134, 239, 180, 149)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "beq_eq_true_of_eq"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(167, 171, 207, 135, 144, 97, 123, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqUp___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(35, 188, 189, 31, 103, 102, 90, 237)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBEqDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_of_beq_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBEqDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 117, 230, 167, 164, 196, 163, 155)}};
static const lean_object* l_Lean_Meta_Grind_propagateBEqDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBEqDown___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateHEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateHEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_propagateIte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateIte___closed__0;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ite_eq_right_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 223, 35, 242, 130, 83, 13)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_eq_left_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 84, 15, 184, 226, 12, 142, 9)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dite_cond_eq_false'"};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 208, 133, 179, 87, 251, 158, 198)}};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_true'"};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(80, 52, 77, 107, 134, 38, 67, 128)}};
static const lean_object* l_Lean_Meta_Grind_propagateDIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDIte___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__7_value),LEAN_SCALAR_PTR_LITERAL(182, 147, 228, 248, 61, 236, 36, 195)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateDecideDown___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideDown___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideDown___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__10_value),LEAN_SCALAR_PTR_LITERAL(244, 38, 211, 128, 18, 129, 201, 136)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideDown___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateDecideDown___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateDecideDown___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateDecideUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "decide_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 47, 57, 153, 34, 139, 245, 136)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateDecideUp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateDecideUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "decide_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateDecideUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 82, 55, 141, 31, 164, 57, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateDecideUp___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateDecideUp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateDecideUp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 175, 130, 140, 152, 16, 186, 53)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndUp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__7_value),LEAN_SCALAR_PTR_LITERAL(163, 211, 47, 64, 193, 141, 13, 161)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndUp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(34, 225, 220, 139, 38, 192, 9, 42)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__7;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__13_value),LEAN_SCALAR_PTR_LITERAL(55, 49, 202, 191, 5, 220, 111, 69)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndUp___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 119, 163, 136, 179, 150, 159, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndDown___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateAndDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(75, 159, 33, 77, 90, 187, 137, 39)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolAndDown___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolAndDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 189, 183, 67, 38, 153, 146, 222)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrUp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(153, 186, 97, 237, 168, 207, 131, 131)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrUp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(128, 97, 38, 173, 77, 149, 251, 177)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__7;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(85, 94, 73, 24, 179, 253, 130, 70)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrUp___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 8, 66, 25, 166, 142, 103, 182)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrDown___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateOrDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(181, 34, 184, 188, 120, 43, 145, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolOrDown___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolOrDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 46, 223, 118, 64, 152, 39, 57)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__3;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 77, 139, 157, 220, 88, 43, 11)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolNotUp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__5;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(244, 210, 8, 221, 13, 95, 8, 117)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolNotUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 229, 82, 105, 115, 174, 156, 45)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolNotDown___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 167, 111, 252, 241, 49, 201, 184)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_propagateNotDown___closed__3_value),LEAN_SCALAR_PTR_LITERAL(213, 82, 102, 124, 79, 254, 235, 150)}};
static const lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBoolNotDown___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateBoolNotDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__6(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_box(0);
v___x_12_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__5));
v___x_13_ = l_Lean_mkConst(v___x_12_, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__9(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_box(0);
v___x_20_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__8));
v___x_21_ = l_Lean_mkConst(v___x_20_, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__11));
v___x_29_ = l_Lean_mkConst(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndUp___closed__15(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_box(0);
v___x_36_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__14));
v___x_37_ = l_Lean_mkConst(v___x_36_, v___x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
lean_inc_ref(v_e_38_);
v___x_53_ = l_Lean_Expr_cleanupAnnotations(v_e_38_);
v___x_54_ = l_Lean_Expr_isApp(v___x_53_);
if (v___x_54_ == 0)
{
lean_dec_ref(v___x_53_);
lean_dec_ref(v_e_38_);
goto v___jp_50_;
}
else
{
lean_object* v_arg_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_arg_55_ = lean_ctor_get(v___x_53_, 1);
lean_inc_ref(v_arg_55_);
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_53_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_56_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
goto v___jp_50_;
}
else
{
lean_object* v_arg_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_arg_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc_ref(v_arg_58_);
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_60_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_61_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_60_);
lean_dec_ref(v___x_59_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
goto v___jp_50_;
}
else
{
lean_object* v___x_62_; 
lean_inc_ref(v_arg_58_);
v___x_62_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_58_, v_a_39_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; uint8_t v___x_64_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_62_, 1);
v___x_64_ = lean_unbox(v_a_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; 
lean_inc_ref(v_arg_55_);
v___x_65_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_55_, v_a_39_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; uint8_t v___x_67_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
v___x_67_ = lean_unbox(v_a_66_);
lean_dec(v_a_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; 
lean_dec(v_a_63_);
lean_inc_ref(v_arg_58_);
v___x_68_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_58_, v_a_39_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; uint8_t v___x_70_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = lean_unbox(v_a_69_);
lean_dec(v_a_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_inc_ref(v_arg_55_);
v___x_71_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_55_, v_a_39_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_94_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_94_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_94_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_94_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint8_t v___x_76_; 
v___x_76_ = lean_unbox(v_a_72_);
lean_dec(v_a_72_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_79_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v___x_77_ = lean_box(0);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_77_);
v___x_79_ = v___x_74_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
else
{
lean_object* v___x_81_; 
lean_del_object(v___x_74_);
lean_inc_ref(v_arg_55_);
v___x_81_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_55_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndUp___closed__6, &l_Lean_Meta_Grind_propagateAndUp___closed__6_once, _init_l_Lean_Meta_Grind_propagateAndUp___closed__6);
v___x_84_ = l_Lean_mkApp3(v___x_83_, v_arg_58_, v_arg_55_, v_a_82_);
v___x_85_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_38_, v___x_84_, v_a_39_, v_a_41_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
return v___x_85_;
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_86_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_81_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_95_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_71_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_71_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_object* v___x_103_; 
lean_inc_ref(v_arg_58_);
v___x_103_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_58_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndUp___closed__9, &l_Lean_Meta_Grind_propagateAndUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateAndUp___closed__9);
v___x_106_ = l_Lean_mkApp3(v___x_105_, v_arg_58_, v_arg_55_, v_a_104_);
v___x_107_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_38_, v___x_106_, v_a_39_, v_a_41_, v_a_43_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_108_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_103_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_103_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_116_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_68_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_68_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v___x_124_; 
lean_inc_ref(v_arg_55_);
v___x_124_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_55_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndUp___closed__12, &l_Lean_Meta_Grind_propagateAndUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateAndUp___closed__12);
lean_inc_ref(v_arg_58_);
v___x_127_ = l_Lean_mkApp3(v___x_126_, v_arg_58_, v_arg_55_, v_a_125_);
v___x_128_ = lean_unbox(v_a_63_);
lean_dec(v_a_63_);
v___x_129_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_38_, v_arg_58_, v___x_127_, v___x_128_, v_a_39_, v_a_41_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_a_63_);
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_130_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_124_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_124_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_63_);
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_138_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_65_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_65_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v___x_146_; 
lean_dec(v_a_63_);
lean_inc_ref(v_arg_58_);
v___x_146_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_58_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_146_, 1);
v___x_148_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndUp___closed__15, &l_Lean_Meta_Grind_propagateAndUp___closed__15_once, _init_l_Lean_Meta_Grind_propagateAndUp___closed__15);
lean_inc_ref(v_arg_55_);
v___x_149_ = l_Lean_mkApp3(v___x_148_, v_arg_58_, v_arg_55_, v_a_147_);
v___x_150_ = 0;
v___x_151_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_38_, v_arg_55_, v___x_149_, v___x_150_, v_a_39_, v_a_41_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
return v___x_151_;
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_152_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_146_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_146_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_arg_58_);
lean_dec_ref(v_arg_55_);
lean_dec_ref(v_e_38_);
v_a_160_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_62_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_62_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
v___jp_50_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___boxed(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_Grind_propagateAndUp(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec(v_a_169_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndUp___boxed), 12, 0);
v___x_184_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_();
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__2(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(0);
v___x_193_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__1));
v___x_194_ = l_Lean_mkConst(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__5(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_box(0);
v___x_201_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__4));
v___x_202_ = l_Lean_mkConst(v___x_201_, v___x_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_218_; 
lean_inc_ref(v_e_203_);
v___x_218_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_203_, v_a_204_, v_a_208_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_253_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_253_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_253_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_253_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = lean_unbox(v_a_219_);
lean_dec(v_a_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_dec_ref(v_e_203_);
v___x_224_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
else
{
lean_object* v___x_228_; uint8_t v___x_229_; 
lean_del_object(v___x_221_);
lean_inc_ref(v_e_203_);
v___x_228_ = l_Lean_Expr_cleanupAnnotations(v_e_203_);
v___x_229_ = l_Lean_Expr_isApp(v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v___x_228_);
lean_dec_ref(v_e_203_);
goto v___jp_215_;
}
else
{
lean_object* v_arg_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_arg_230_ = lean_ctor_get(v___x_228_, 1);
lean_inc_ref(v_arg_230_);
v___x_231_ = l_Lean_Expr_appFnCleanup___redArg(v___x_228_);
v___x_232_ = l_Lean_Expr_isApp(v___x_231_);
if (v___x_232_ == 0)
{
lean_dec_ref(v___x_231_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_e_203_);
goto v___jp_215_;
}
else
{
lean_object* v_arg_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_arg_233_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_arg_233_);
v___x_234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_231_);
v___x_235_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_236_ = l_Lean_Expr_isConstOf(v___x_234_, v___x_235_);
lean_dec_ref(v___x_234_);
if (v___x_236_ == 0)
{
lean_dec_ref(v_arg_233_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_e_203_);
goto v___jp_215_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc_n(v_a_238_, 2);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndDown___closed__2, &l_Lean_Meta_Grind_propagateAndDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateAndDown___closed__2);
lean_inc_ref(v_arg_230_);
lean_inc_ref_n(v_arg_233_, 2);
v___x_240_ = l_Lean_mkApp3(v___x_239_, v_arg_233_, v_arg_230_, v_a_238_);
v___x_241_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_233_, v___x_240_, v_a_204_, v_a_206_, v_a_208_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_242_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndDown___closed__5, &l_Lean_Meta_Grind_propagateAndDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateAndDown___closed__5);
lean_inc_ref(v_arg_230_);
v___x_243_ = l_Lean_mkApp3(v___x_242_, v_arg_233_, v_arg_230_, v_a_238_);
v___x_244_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_230_, v___x_243_, v_a_204_, v_a_206_, v_a_208_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
return v___x_244_;
}
else
{
lean_dec(v_a_238_);
lean_dec_ref(v_arg_233_);
lean_dec_ref(v_arg_230_);
return v___x_241_;
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_arg_233_);
lean_dec_ref(v_arg_230_);
v_a_245_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_237_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_237_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
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
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_e_203_);
v_a_254_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_218_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_218_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___boxed(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_propagateAndDown(v_e_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec(v_a_263_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_277_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndDown___boxed), 12, 0);
v___x_278_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9____boxed(lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_();
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__4(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_box(0);
v___x_290_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__3));
v___x_291_ = l_Lean_mkConst(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__7(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__6));
v___x_299_ = l_Lean_mkConst(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__10(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__9));
v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__13(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_box(0);
v___x_314_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__12));
v___x_315_ = l_Lean_mkConst(v___x_314_, v___x_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
lean_inc_ref(v_e_316_);
v___x_331_ = l_Lean_Expr_cleanupAnnotations(v_e_316_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v_e_316_);
goto v___jp_328_;
}
else
{
lean_object* v_arg_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_arg_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_arg_333_);
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_335_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
goto v___jp_328_;
}
else
{
lean_object* v_arg_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_arg_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc_ref(v_arg_336_);
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_338_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
lean_dec_ref(v___x_337_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
goto v___jp_328_;
}
else
{
lean_object* v___x_340_; 
lean_inc_ref(v_arg_336_);
v___x_340_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_336_, v_a_317_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; uint8_t v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = lean_unbox(v_a_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_inc_ref(v_arg_333_);
v___x_343_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_333_, v_a_317_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; uint8_t v___x_345_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = lean_unbox(v_a_344_);
lean_dec(v_a_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_dec(v_a_341_);
lean_inc_ref(v_arg_336_);
v___x_346_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_336_, v_a_317_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; uint8_t v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = lean_unbox(v_a_347_);
lean_dec(v_a_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_inc_ref(v_arg_333_);
v___x_349_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_333_, v_a_317_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_372_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_372_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_372_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_372_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_a_350_);
lean_dec(v_a_350_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v___x_355_ = lean_box(0);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_355_);
v___x_357_ = v___x_352_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
else
{
lean_object* v___x_359_; 
lean_del_object(v___x_352_);
lean_inc_ref(v_arg_333_);
v___x_359_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_333_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v___x_361_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__4, &l_Lean_Meta_Grind_propagateOrUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__4);
v___x_362_ = l_Lean_mkApp3(v___x_361_, v_arg_336_, v_arg_333_, v_a_360_);
v___x_363_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_316_, v___x_362_, v_a_317_, v_a_319_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_363_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_364_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_359_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_359_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_373_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_349_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_349_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v___x_381_; 
lean_inc_ref(v_arg_336_);
v___x_381_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__7, &l_Lean_Meta_Grind_propagateOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__7);
v___x_384_ = l_Lean_mkApp3(v___x_383_, v_arg_336_, v_arg_333_, v_a_382_);
v___x_385_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_316_, v___x_384_, v_a_317_, v_a_319_, v_a_321_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_386_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_381_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_394_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_346_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_346_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v___x_402_; 
lean_inc_ref(v_arg_333_);
v___x_402_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_333_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__10, &l_Lean_Meta_Grind_propagateOrUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__10);
lean_inc_ref(v_arg_336_);
v___x_405_ = l_Lean_mkApp3(v___x_404_, v_arg_336_, v_arg_333_, v_a_403_);
v___x_406_ = lean_unbox(v_a_341_);
lean_dec(v_a_341_);
v___x_407_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_316_, v_arg_336_, v___x_405_, v___x_406_, v_a_317_, v_a_319_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_407_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_a_341_);
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_408_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_402_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_402_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_a_341_);
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_416_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_343_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_343_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v___x_424_; 
lean_dec(v_a_341_);
lean_inc_ref(v_arg_336_);
v___x_424_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_336_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__13, &l_Lean_Meta_Grind_propagateOrUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__13);
lean_inc_ref(v_arg_333_);
v___x_427_ = l_Lean_mkApp3(v___x_426_, v_arg_336_, v_arg_333_, v_a_425_);
v___x_428_ = 0;
v___x_429_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_316_, v_arg_333_, v___x_427_, v___x_428_, v_a_317_, v_a_319_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_429_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_430_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_424_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_333_);
lean_dec_ref(v_e_316_);
v_a_438_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_340_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_340_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
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
}
}
v___jp_328_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___boxed(lean_object* v_e_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Grind_propagateOrUp(v_e_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrUp___boxed), 12, 0);
v___x_462_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_460_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9____boxed(lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_();
return v_res_464_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__2(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__1));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__5(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__4));
v___x_480_ = l_Lean_mkConst(v___x_479_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object* v_e_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_496_; 
lean_inc_ref(v_e_481_);
v___x_496_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_481_, v_a_482_, v_a_486_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_531_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_531_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_531_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_531_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; 
v___x_501_ = lean_unbox(v_a_497_);
lean_dec(v_a_497_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec_ref(v_e_481_);
v___x_502_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
lean_del_object(v___x_499_);
lean_inc_ref(v_e_481_);
v___x_506_ = l_Lean_Expr_cleanupAnnotations(v_e_481_);
v___x_507_ = l_Lean_Expr_isApp(v___x_506_);
if (v___x_507_ == 0)
{
lean_dec_ref(v___x_506_);
lean_dec_ref(v_e_481_);
goto v___jp_493_;
}
else
{
lean_object* v_arg_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_arg_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc_ref(v_arg_508_);
v___x_509_ = l_Lean_Expr_appFnCleanup___redArg(v___x_506_);
v___x_510_ = l_Lean_Expr_isApp(v___x_509_);
if (v___x_510_ == 0)
{
lean_dec_ref(v___x_509_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_e_481_);
goto v___jp_493_;
}
else
{
lean_object* v_arg_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_arg_511_ = lean_ctor_get(v___x_509_, 1);
lean_inc_ref(v_arg_511_);
v___x_512_ = l_Lean_Expr_appFnCleanup___redArg(v___x_509_);
v___x_513_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_514_ = l_Lean_Expr_isConstOf(v___x_512_, v___x_513_);
lean_dec_ref(v___x_512_);
if (v___x_514_ == 0)
{
lean_dec_ref(v_arg_511_);
lean_dec_ref(v_arg_508_);
lean_dec_ref(v_e_481_);
goto v___jp_493_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_n(v_a_516_, 2);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrDown___closed__2, &l_Lean_Meta_Grind_propagateOrDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateOrDown___closed__2);
lean_inc_ref(v_arg_508_);
lean_inc_ref_n(v_arg_511_, 2);
v___x_518_ = l_Lean_mkApp3(v___x_517_, v_arg_511_, v_arg_508_, v_a_516_);
v___x_519_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_511_, v___x_518_, v_a_482_, v_a_484_, v_a_486_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrDown___closed__5, &l_Lean_Meta_Grind_propagateOrDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateOrDown___closed__5);
lean_inc_ref(v_arg_508_);
v___x_521_ = l_Lean_mkApp3(v___x_520_, v_arg_511_, v_arg_508_, v_a_516_);
v___x_522_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_508_, v___x_521_, v_a_482_, v_a_484_, v_a_486_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
return v___x_522_;
}
else
{
lean_dec(v_a_516_);
lean_dec_ref(v_arg_511_);
lean_dec_ref(v_arg_508_);
return v___x_519_;
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_arg_511_);
lean_dec_ref(v_arg_508_);
v_a_523_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_515_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
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
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_e_481_);
v_a_532_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_496_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_496_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
v___jp_493_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___boxed(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Grind_propagateOrDown(v_e_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec(v_a_541_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_555_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrDown___boxed), 12, 0);
v___x_556_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9____boxed(lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_();
return v_res_558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__4(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_box(0);
v___x_568_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__3));
v___x_569_ = l_Lean_mkConst(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__7(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__6));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__10(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__9));
v___x_585_ = l_Lean_mkConst(v___x_584_, v___x_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object* v_e_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
lean_inc_ref(v_e_586_);
v___x_601_ = l_Lean_Expr_cleanupAnnotations(v_e_586_);
v___x_602_ = l_Lean_Expr_isApp(v___x_601_);
if (v___x_602_ == 0)
{
lean_dec_ref(v___x_601_);
lean_dec_ref(v_e_586_);
goto v___jp_598_;
}
else
{
lean_object* v_arg_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_arg_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc_ref(v_arg_603_);
v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_601_);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_606_ = l_Lean_Expr_isConstOf(v___x_604_, v___x_605_);
lean_dec_ref(v___x_604_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
goto v___jp_598_;
}
else
{
lean_object* v___x_607_; 
lean_inc_ref(v_arg_603_);
v___x_607_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_603_, v_a_587_, v_a_591_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; uint8_t v___x_609_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_inc_ref(v_arg_603_);
v___x_610_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_603_, v_a_587_, v_a_591_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; uint8_t v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_unbox(v_a_611_);
lean_dec(v_a_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_586_, v_arg_603_, v_a_587_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_636_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_636_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_636_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_636_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_unbox(v_a_614_);
lean_dec(v_a_614_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v___x_619_ = lean_box(0);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; 
lean_del_object(v___x_616_);
lean_inc(v_a_596_);
lean_inc_ref(v_a_595_);
lean_inc(v_a_594_);
lean_inc_ref(v_a_593_);
lean_inc(v_a_592_);
lean_inc_ref(v_a_591_);
lean_inc(v_a_590_);
lean_inc_ref(v_a_589_);
lean_inc(v_a_588_);
lean_inc(v_a_587_);
lean_inc_ref(v_arg_603_);
v___x_623_ = lean_grind_mk_eq_proof(v_e_586_, v_arg_603_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__4, &l_Lean_Meta_Grind_propagateNotUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__4);
v___x_626_ = l_Lean_mkAppB(v___x_625_, v_arg_603_, v_a_624_);
v___x_627_ = l_Lean_Meta_Grind_closeGoal(v___x_626_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_627_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_arg_603_);
v_a_628_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_623_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_623_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v_a_637_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_613_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_613_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v___x_645_; 
lean_inc_ref(v_arg_603_);
v___x_645_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_603_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__7, &l_Lean_Meta_Grind_propagateNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__7);
v___x_648_ = l_Lean_mkAppB(v___x_647_, v_arg_603_, v_a_646_);
v___x_649_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_586_, v___x_648_, v_a_587_, v_a_589_, v_a_591_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_649_;
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v_a_650_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_645_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_645_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
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
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v_a_658_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_610_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_610_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v___x_666_; 
lean_inc_ref(v_arg_603_);
v___x_666_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_603_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__10, &l_Lean_Meta_Grind_propagateNotUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__10);
v___x_669_ = l_Lean_mkAppB(v___x_668_, v_arg_603_, v_a_667_);
v___x_670_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_586_, v___x_669_, v_a_587_, v_a_589_, v_a_591_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
return v___x_670_;
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v_a_671_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_666_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_666_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_arg_603_);
lean_dec_ref(v_e_586_);
v_a_679_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_607_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_607_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
v___jp_598_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___boxed(lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_Grind_propagateNotUp(v_e_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_a_688_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_702_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotUp___boxed), 12, 0);
v___x_703_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9____boxed(lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_();
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__2(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_box(0);
v___x_712_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__1));
v___x_713_ = l_Lean_mkConst(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__5(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__4));
v___x_721_ = l_Lean_mkConst(v___x_720_, v___x_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object* v_e_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
lean_inc_ref(v_e_722_);
v___x_737_ = l_Lean_Expr_cleanupAnnotations(v_e_722_);
v___x_738_ = l_Lean_Expr_isApp(v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v___x_737_);
lean_dec_ref(v_e_722_);
goto v___jp_734_;
}
else
{
lean_object* v_arg_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_arg_739_ = lean_ctor_get(v___x_737_, 1);
lean_inc_ref(v_arg_739_);
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_737_);
v___x_741_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_742_ = l_Lean_Expr_isConstOf(v___x_740_, v___x_741_);
lean_dec_ref(v___x_740_);
if (v___x_742_ == 0)
{
lean_dec_ref(v_arg_739_);
lean_dec_ref(v_e_722_);
goto v___jp_734_;
}
else
{
lean_object* v___x_743_; 
lean_inc_ref(v_e_722_);
v___x_743_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_722_, v_a_723_, v_a_727_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; uint8_t v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = lean_unbox(v_a_744_);
lean_dec(v_a_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_inc_ref(v_e_722_);
v___x_746_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_722_, v_a_723_, v_a_727_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_722_, v_arg_739_, v_a_723_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_772_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_772_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_772_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_772_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; 
v___x_754_ = lean_unbox(v_a_750_);
lean_dec(v_a_750_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec_ref(v_arg_739_);
lean_dec_ref(v_e_722_);
v___x_755_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v___x_759_; 
lean_del_object(v___x_752_);
lean_inc(v_a_732_);
lean_inc_ref(v_a_731_);
lean_inc(v_a_730_);
lean_inc_ref(v_a_729_);
lean_inc(v_a_728_);
lean_inc_ref(v_a_727_);
lean_inc(v_a_726_);
lean_inc_ref(v_a_725_);
lean_inc(v_a_724_);
lean_inc(v_a_723_);
lean_inc_ref(v_arg_739_);
v___x_759_ = lean_grind_mk_eq_proof(v_e_722_, v_arg_739_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__4, &l_Lean_Meta_Grind_propagateNotUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__4);
v___x_762_ = l_Lean_mkAppB(v___x_761_, v_arg_739_, v_a_760_);
v___x_763_ = l_Lean_Meta_Grind_closeGoal(v___x_762_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_763_;
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v_arg_739_);
v_a_764_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_759_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_arg_739_);
lean_dec_ref(v_e_722_);
v_a_773_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_749_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_749_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotDown___closed__2, &l_Lean_Meta_Grind_propagateNotDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateNotDown___closed__2);
lean_inc_ref(v_arg_739_);
v___x_784_ = l_Lean_mkAppB(v___x_783_, v_arg_739_, v_a_782_);
v___x_785_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_739_, v___x_784_, v_a_723_, v_a_725_, v_a_727_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_785_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_arg_739_);
v_a_786_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_781_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_781_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_arg_739_);
lean_dec_ref(v_e_722_);
v_a_794_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_746_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_746_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotDown___closed__5, &l_Lean_Meta_Grind_propagateNotDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateNotDown___closed__5);
lean_inc_ref(v_arg_739_);
v___x_805_ = l_Lean_mkAppB(v___x_804_, v_arg_739_, v_a_803_);
v___x_806_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_739_, v___x_805_, v_a_723_, v_a_725_, v_a_727_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_arg_739_);
v_a_807_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_802_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec_ref(v_arg_739_);
lean_dec_ref(v_e_722_);
v_a_815_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_743_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_743_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
v___jp_734_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___boxed(lean_object* v_e_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Meta_Grind_propagateNotDown(v_e_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec(v_a_824_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_838_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotDown___boxed), 12, 0);
v___x_839_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_837_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9____boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_();
return v_res_841_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__2));
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v___x_859_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__5));
v___x_860_ = l_Lean_mkConst(v___x_859_, v___x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object* v_eq_861_, lean_object* v_a_862_, lean_object* v_b_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_868_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
v___x_877_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_868_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_863_, v_a_878_, v_a_864_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; uint8_t v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = lean_unbox(v_a_880_);
lean_dec(v_a_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_863_, v_a_876_, v_a_864_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; uint8_t v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = lean_unbox(v_a_883_);
lean_dec(v_a_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_862_, v_a_878_, v_a_864_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v_a_878_);
v___x_888_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_862_, v_a_876_, v_a_864_);
lean_dec_ref(v_a_862_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_911_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_911_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_911_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_911_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___x_893_; 
v___x_893_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_eq_861_);
v___x_894_ = lean_box(0);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v___x_898_; 
lean_del_object(v___x_891_);
lean_inc_ref(v_b_863_);
v___x_898_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_b_863_, v_a_876_, v_eq_861_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__3, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3);
lean_inc_ref(v_b_863_);
v___x_901_ = l_Lean_mkAppB(v___x_900_, v_b_863_, v_a_899_);
v___x_902_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_b_863_, v___x_901_, v_a_864_, v_a_866_, v_a_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_b_863_);
v_a_903_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_898_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_eq_861_);
v_a_912_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_888_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_888_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_a_876_);
lean_dec_ref(v_a_862_);
lean_inc_ref(v_b_863_);
v___x_920_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_b_863_, v_a_878_, v_eq_861_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__6, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__6_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6);
lean_inc_ref(v_b_863_);
v___x_923_ = l_Lean_mkAppB(v___x_922_, v_b_863_, v_a_921_);
v___x_924_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_b_863_, v___x_923_, v_a_864_, v_a_866_, v_a_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_924_;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_b_863_);
v_a_925_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_878_);
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_eq_861_);
v_a_933_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_885_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_885_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v___x_941_; 
lean_dec(v_a_878_);
lean_dec_ref(v_b_863_);
lean_inc_ref(v_a_862_);
v___x_941_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_862_, v_a_876_, v_eq_861_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__3, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3);
lean_inc_ref(v_a_862_);
v___x_944_ = l_Lean_mkAppB(v___x_943_, v_a_862_, v_a_942_);
v___x_945_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_a_862_, v___x_944_, v_a_864_, v_a_866_, v_a_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_945_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v_a_862_);
v_a_946_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_941_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_a_878_);
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_eq_861_);
v_a_954_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_882_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_882_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_inc_ref(v_a_862_);
v___x_962_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_862_, v_a_878_, v_eq_861_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__6, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__6_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6);
lean_inc_ref(v_a_862_);
v___x_965_ = l_Lean_mkAppB(v___x_964_, v_a_862_, v_a_963_);
v___x_966_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_a_862_, v___x_965_, v_a_864_, v_a_866_, v_a_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
return v___x_966_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_a_862_);
v_a_967_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_962_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_878_);
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_eq_861_);
v_a_975_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_879_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_879_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_876_);
lean_dec_ref(v_b_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_eq_861_);
v_a_983_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_877_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_877_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_b_863_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_eq_861_);
v_a_991_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_875_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_875_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___boxed(lean_object* v_eq_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_eq_999_, v_a_1000_, v_b_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec(v_a_1002_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(uint8_t v_a_1014_, uint8_t v___x_1015_, lean_object* v_self_1016_, lean_object* v_arg_1017_, lean_object* v_arg_1018_, lean_object* v_self_1019_, lean_object* v_hab_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_hf_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___x_1061_; 
lean_inc_ref(v_self_1016_);
lean_inc_ref(v_arg_1017_);
v___x_1061_ = l_Lean_Meta_Grind_hasSameType(v_arg_1017_, v_self_1016_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
lean_inc_ref(v_self_1019_);
lean_inc_ref(v_arg_1018_);
v___x_1063_ = l_Lean_Meta_Grind_hasSameType(v_arg_1018_, v_self_1019_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1063_) == 0)
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_unbox(v_a_1062_);
lean_dec(v_a_1062_);
if (v___x_1064_ == 1)
{
lean_object* v_a_1065_; uint8_t v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1066_ = lean_unbox(v_a_1065_);
lean_dec(v_a_1065_);
if (v___x_1066_ == 1)
{
lean_object* v___x_1067_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc(v___y_1021_);
v___x_1067_ = lean_grind_mk_eq_proof(v_self_1016_, v_arg_1017_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
lean_inc_ref(v_hab_1020_);
v___x_1069_ = l_Lean_Meta_mkEqTrans(v_a_1068_, v_hab_1020_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc(v___y_1021_);
v___x_1071_ = lean_grind_mk_eq_proof(v_arg_1018_, v_self_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Lean_Meta_mkEqTrans(v_a_1070_, v_a_1072_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_hf_1033_ = v_a_1074_;
v___y_1034_ = v___y_1025_;
v___y_1035_ = v___y_1027_;
v___y_1036_ = v___y_1028_;
v___y_1037_ = v___y_1029_;
v___y_1038_ = v___y_1030_;
goto v___jp_1032_;
}
else
{
lean_dec_ref(v_hab_1020_);
return v___x_1073_;
}
}
else
{
lean_dec(v_a_1070_);
lean_dec_ref(v_hab_1020_);
return v___x_1071_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
return v___x_1069_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
return v___x_1067_;
}
}
else
{
goto v___jp_1048_;
}
}
else
{
lean_dec_ref_known(v___x_1063_, 1);
goto v___jp_1048_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
lean_dec_ref(v_arg_1017_);
lean_dec_ref(v_self_1016_);
v_a_1075_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1063_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1063_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
lean_dec_ref(v_arg_1017_);
lean_dec_ref(v_self_1016_);
v_a_1083_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1061_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1061_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
v___jp_1032_:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1034_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Meta_mkNoConfusion(v_a_1040_, v_hf_1033_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_mk_empty_array_with_capacity(v___x_1043_);
v___x_1045_ = lean_array_push(v___x_1044_, v_hab_1020_);
v___x_1046_ = 1;
v___x_1047_ = l_Lean_Meta_mkLambdaFVars(v___x_1045_, v_a_1042_, v_a_1014_, v___x_1015_, v_a_1014_, v___x_1015_, v___x_1046_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v___x_1045_);
return v___x_1047_;
}
else
{
lean_dec_ref(v_hab_1020_);
return v___x_1041_;
}
}
else
{
lean_dec_ref(v_hf_1033_);
lean_dec_ref(v_hab_1020_);
return v___x_1039_;
}
}
v___jp_1048_:
{
lean_object* v___x_1049_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc(v___y_1021_);
v___x_1049_ = lean_grind_mk_heq_proof(v_self_1016_, v_arg_1017_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
lean_inc_ref(v_hab_1020_);
v___x_1051_ = l_Lean_Meta_mkHEqOfEq(v_hab_1020_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_Meta_mkHEqTrans(v_a_1050_, v_a_1052_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc(v___y_1021_);
v___x_1055_ = lean_grind_mk_heq_proof(v_arg_1018_, v_self_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1057_ = l_Lean_Meta_mkHEqTrans(v_a_1054_, v_a_1056_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = l_Lean_Meta_mkEqOfHEq(v_a_1058_, v___x_1015_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v_hf_1033_ = v_a_1060_;
v___y_1034_ = v___y_1025_;
v___y_1035_ = v___y_1027_;
v___y_1036_ = v___y_1028_;
v___y_1037_ = v___y_1029_;
v___y_1038_ = v___y_1030_;
goto v___jp_1032_;
}
else
{
lean_dec_ref(v_hab_1020_);
return v___x_1059_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
return v___x_1057_;
}
}
else
{
lean_dec(v_a_1054_);
lean_dec_ref(v_hab_1020_);
return v___x_1055_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
return v___x_1053_;
}
}
else
{
lean_dec(v_a_1050_);
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
return v___x_1051_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1019_);
lean_dec_ref(v_arg_1018_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object** _args){
lean_object* v_a_1091_ = _args[0];
lean_object* v___x_1092_ = _args[1];
lean_object* v_self_1093_ = _args[2];
lean_object* v_arg_1094_ = _args[3];
lean_object* v_arg_1095_ = _args[4];
lean_object* v_self_1096_ = _args[5];
lean_object* v_hab_1097_ = _args[6];
lean_object* v___y_1098_ = _args[7];
lean_object* v___y_1099_ = _args[8];
lean_object* v___y_1100_ = _args[9];
lean_object* v___y_1101_ = _args[10];
lean_object* v___y_1102_ = _args[11];
lean_object* v___y_1103_ = _args[12];
lean_object* v___y_1104_ = _args[13];
lean_object* v___y_1105_ = _args[14];
lean_object* v___y_1106_ = _args[15];
lean_object* v___y_1107_ = _args[16];
lean_object* v___y_1108_ = _args[17];
_start:
{
uint8_t v_a_111367__boxed_1109_; uint8_t v___x_111368__boxed_1110_; lean_object* v_res_1111_; 
v_a_111367__boxed_1109_ = lean_unbox(v_a_1091_);
v___x_111368__boxed_1110_ = lean_unbox(v___x_1092_);
v_res_1111_ = l_Lean_Meta_Grind_propagateEqUp___lam__0(v_a_111367__boxed_1109_, v___x_111368__boxed_1110_, v_self_1093_, v_arg_1094_, v_arg_1095_, v_self_1096_, v_hab_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___y_1098_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v_b_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1118_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1114_);
lean_inc(v___y_1113_);
v___x_1125_ = lean_apply_12(v_k_1112_, v_b_1119_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, lean_box(0));
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(v_k_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v_b_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec(v___y_1127_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object* v_name_1140_, uint8_t v_bi_1141_, lean_object* v_type_1142_, lean_object* v_k_1143_, uint8_t v_kind_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___f_1156_; lean_object* v___x_1157_; 
lean_inc(v___y_1150_);
lean_inc_ref(v___y_1149_);
lean_inc(v___y_1148_);
lean_inc_ref(v___y_1147_);
lean_inc(v___y_1146_);
lean_inc(v___y_1145_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1156_, 0, v_k_1143_);
lean_closure_set(v___f_1156_, 1, v___y_1145_);
lean_closure_set(v___f_1156_, 2, v___y_1146_);
lean_closure_set(v___f_1156_, 3, v___y_1147_);
lean_closure_set(v___f_1156_, 4, v___y_1148_);
lean_closure_set(v___f_1156_, 5, v___y_1149_);
lean_closure_set(v___f_1156_, 6, v___y_1150_);
v___x_1157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1140_, v_bi_1141_, v_type_1142_, v___f_1156_, v_kind_1144_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1157_) == 0)
{
return v___x_1157_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object* v_name_1166_, lean_object* v_bi_1167_, lean_object* v_type_1168_, lean_object* v_k_1169_, lean_object* v_kind_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_bi_boxed_1182_; uint8_t v_kind_boxed_1183_; lean_object* v_res_1184_; 
v_bi_boxed_1182_ = lean_unbox(v_bi_1167_);
v_kind_boxed_1183_ = lean_unbox(v_kind_1170_);
v_res_1184_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1166_, v_bi_boxed_1182_, v_type_1168_, v_k_1169_, v_kind_boxed_1183_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec(v___y_1171_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object* v_name_1185_, lean_object* v_type_1186_, lean_object* v_k_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = 0;
v___x_1200_ = 0;
v___x_1201_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1185_, v___x_1199_, v_type_1186_, v_k_1187_, v___x_1200_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object* v_name_1202_, lean_object* v_type_1203_, lean_object* v_k_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_1202_, v_type_1203_, v_k_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(uint8_t v_a_1217_, uint8_t v___x_1218_, lean_object* v_self_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_self_1222_, lean_object* v_hab_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_hf_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___x_1264_; 
lean_inc_ref(v_self_1219_);
lean_inc_ref(v_a_1220_);
v___x_1264_ = l_Lean_Meta_Grind_hasSameType(v_a_1220_, v_self_1219_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1266_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
lean_inc_ref(v_self_1222_);
lean_inc_ref(v_a_1221_);
v___x_1266_ = l_Lean_Meta_Grind_hasSameType(v_a_1221_, v_self_1222_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1266_) == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
if (v___x_1267_ == 1)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
if (v___x_1269_ == 1)
{
lean_object* v___x_1270_; 
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc(v___y_1224_);
v___x_1270_ = lean_grind_mk_eq_proof(v_self_1219_, v_a_1220_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
lean_inc_ref(v_hab_1223_);
v___x_1272_ = l_Lean_Meta_mkEqTrans(v_a_1271_, v_hab_1223_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc(v___y_1224_);
v___x_1274_ = lean_grind_mk_eq_proof(v_a_1221_, v_self_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l_Lean_Meta_mkEqTrans(v_a_1273_, v_a_1275_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v_hf_1236_ = v_a_1277_;
v___y_1237_ = v___y_1228_;
v___y_1238_ = v___y_1230_;
v___y_1239_ = v___y_1231_;
v___y_1240_ = v___y_1232_;
v___y_1241_ = v___y_1233_;
goto v___jp_1235_;
}
else
{
lean_dec_ref(v_hab_1223_);
return v___x_1276_;
}
}
else
{
lean_dec(v_a_1273_);
lean_dec_ref(v_hab_1223_);
return v___x_1274_;
}
}
else
{
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
return v___x_1272_;
}
}
else
{
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
return v___x_1270_;
}
}
else
{
goto v___jp_1251_;
}
}
else
{
lean_dec_ref_known(v___x_1266_, 1);
goto v___jp_1251_;
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1265_);
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_self_1219_);
v_a_1278_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1266_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1266_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec_ref(v_self_1219_);
v_a_1286_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1264_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1264_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
v___jp_1235_:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1237_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Meta_mkNoConfusion(v_a_1243_, v_hf_1236_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_mk_empty_array_with_capacity(v___x_1246_);
v___x_1248_ = lean_array_push(v___x_1247_, v_hab_1223_);
v___x_1249_ = 1;
v___x_1250_ = l_Lean_Meta_mkLambdaFVars(v___x_1248_, v_a_1245_, v_a_1217_, v___x_1218_, v_a_1217_, v___x_1218_, v___x_1249_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec_ref(v___x_1248_);
return v___x_1250_;
}
else
{
lean_dec_ref(v_hab_1223_);
return v___x_1244_;
}
}
else
{
lean_dec_ref(v_hf_1236_);
lean_dec_ref(v_hab_1223_);
return v___x_1242_;
}
}
v___jp_1251_:
{
lean_object* v___x_1252_; 
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc(v___y_1224_);
v___x_1252_ = lean_grind_mk_heq_proof(v_self_1219_, v_a_1220_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
lean_inc_ref(v_hab_1223_);
v___x_1254_ = l_Lean_Meta_mkHEqOfEq(v_hab_1223_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_Meta_mkHEqTrans(v_a_1253_, v_a_1255_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc(v___y_1224_);
v___x_1258_ = lean_grind_mk_heq_proof(v_a_1221_, v_self_1222_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = l_Lean_Meta_mkHEqTrans(v_a_1257_, v_a_1259_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l_Lean_Meta_mkEqOfHEq(v_a_1261_, v___x_1218_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_hf_1236_ = v_a_1263_;
v___y_1237_ = v___y_1228_;
v___y_1238_ = v___y_1230_;
v___y_1239_ = v___y_1231_;
v___y_1240_ = v___y_1232_;
v___y_1241_ = v___y_1233_;
goto v___jp_1235_;
}
else
{
lean_dec_ref(v_hab_1223_);
return v___x_1262_;
}
}
else
{
lean_dec_ref(v_hab_1223_);
return v___x_1260_;
}
}
else
{
lean_dec(v_a_1257_);
lean_dec_ref(v_hab_1223_);
return v___x_1258_;
}
}
else
{
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
return v___x_1256_;
}
}
else
{
lean_dec(v_a_1253_);
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
return v___x_1254_;
}
}
else
{
lean_dec_ref(v_hab_1223_);
lean_dec_ref(v_self_1222_);
lean_dec_ref(v_a_1221_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1294_ = _args[0];
lean_object* v___x_1295_ = _args[1];
lean_object* v_self_1296_ = _args[2];
lean_object* v_a_1297_ = _args[3];
lean_object* v_a_1298_ = _args[4];
lean_object* v_self_1299_ = _args[5];
lean_object* v_hab_1300_ = _args[6];
lean_object* v___y_1301_ = _args[7];
lean_object* v___y_1302_ = _args[8];
lean_object* v___y_1303_ = _args[9];
lean_object* v___y_1304_ = _args[10];
lean_object* v___y_1305_ = _args[11];
lean_object* v___y_1306_ = _args[12];
lean_object* v___y_1307_ = _args[13];
lean_object* v___y_1308_ = _args[14];
lean_object* v___y_1309_ = _args[15];
lean_object* v___y_1310_ = _args[16];
lean_object* v___y_1311_ = _args[17];
_start:
{
uint8_t v_a_111668__boxed_1312_; uint8_t v___x_111669__boxed_1313_; lean_object* v_res_1314_; 
v_a_111668__boxed_1312_ = lean_unbox(v_a_1294_);
v___x_111669__boxed_1313_ = lean_unbox(v___x_1295_);
v_res_1314_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(v_a_111668__boxed_1312_, v___x_111669__boxed_1313_, v_self_1296_, v_a_1297_, v_a_1298_, v_self_1299_, v_hab_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1314_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3));
v___x_1323_ = l_Lean_mkConst(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(lean_object* v_a_1324_, lean_object* v_a_1325_, uint8_t v_a_1326_, uint8_t v___x_1327_, lean_object* v_a_1328_, lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1440_; 
v_snd_1342_ = lean_ctor_get(v_a_1330_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_a_1330_, 0);
lean_dec(v_unused_1441_);
v___x_1344_ = v_a_1330_;
v_isShared_1345_ = v_isSharedCheck_1440_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_dec(v_a_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1440_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_st_ref_get(v___y_1331_);
lean_inc(v_snd_1342_);
v___x_1348_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1347_, v_snd_1342_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1431_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1431_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1431_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_self_1353_; lean_object* v_next_1354_; uint8_t v_ctor_1355_; 
v_self_1353_ = lean_ctor_get(v_a_1349_, 0);
lean_inc_ref(v_self_1353_);
v_next_1354_ = lean_ctor_get(v_a_1349_, 1);
lean_inc_ref(v_next_1354_);
v_ctor_1355_ = lean_ctor_get_uint8(v_a_1349_, sizeof(void*)*12 + 2);
lean_dec(v_a_1349_);
if (v_ctor_1355_ == 0)
{
lean_dec_ref(v_self_1353_);
goto v___jp_1356_;
}
else
{
lean_object* v_self_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_self_1370_ = lean_ctor_get(v_a_1325_, 0);
v___x_1371_ = l_Lean_Expr_getAppFn(v_self_1370_);
v___x_1372_ = l_Lean_Expr_getAppFn(v_self_1353_);
v___x_1373_ = lean_expr_eqv(v___x_1371_, v___x_1372_);
lean_dec_ref(v___x_1372_);
lean_dec_ref(v___x_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___f_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_box(v_a_1326_);
v___x_1375_ = lean_box(v___x_1327_);
lean_inc_ref(v_self_1353_);
lean_inc_ref(v_a_1324_);
lean_inc_ref(v_a_1328_);
lean_inc_ref_n(v_self_1370_, 2);
v___f_1376_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1376_, 0, v___x_1374_);
lean_closure_set(v___f_1376_, 1, v___x_1375_);
lean_closure_set(v___f_1376_, 2, v_self_1370_);
lean_closure_set(v___f_1376_, 3, v_a_1328_);
lean_closure_set(v___f_1376_, 4, v_a_1324_);
lean_closure_set(v___f_1376_, 5, v_self_1353_);
v___x_1377_ = l_Lean_Meta_Grind_hasSameType(v_self_1370_, v_self_1353_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; uint8_t v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v___f_1376_);
goto v___jp_1356_;
}
else
{
lean_object* v___x_1380_; 
lean_dec_ref(v_next_1354_);
lean_del_object(v___x_1351_);
lean_del_object(v___x_1344_);
lean_dec_ref(v_a_1325_);
v___x_1380_ = l_Lean_Meta_mkEq(v_a_1328_, v_a_1324_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1));
v___x_1383_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1382_, v_a_1381_, v___f_1376_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4);
lean_inc_ref(v_e_1329_);
v___x_1386_ = l_Lean_mkAppB(v___x_1385_, v_e_1329_, v_a_1384_);
v___x_1387_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1329_, v___x_1386_, v___y_1331_, v___y_1333_, v___y_1335_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1387_, 0);
lean_dec(v_unused_1398_);
v___x_1389_ = v___x_1387_;
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v___x_1387_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1397_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1391_ = lean_box(v___x_1327_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v_snd_1342_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1393_);
v___x_1395_ = v___x_1389_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_snd_1342_);
v_a_1399_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1387_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1387_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_snd_1342_);
lean_dec_ref(v_e_1329_);
v_a_1407_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1383_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1383_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___f_1376_);
lean_dec(v_snd_1342_);
lean_dec_ref(v_e_1329_);
v_a_1415_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1380_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1380_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v___f_1376_);
lean_dec_ref(v_next_1354_);
lean_del_object(v___x_1351_);
lean_del_object(v___x_1344_);
lean_dec(v_snd_1342_);
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_a_1324_);
v_a_1423_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1377_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1377_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_dec_ref(v_self_1353_);
goto v___jp_1356_;
}
}
v___jp_1356_:
{
size_t v___x_1357_; size_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_ptr_addr(v_next_1354_);
v___x_1358_ = lean_ptr_addr(v_a_1324_);
v___x_1359_ = lean_usize_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1361_; 
lean_del_object(v___x_1351_);
lean_dec(v_snd_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v_next_1354_);
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1361_ = v___x_1344_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_next_1354_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v_a_1330_ = v___x_1361_;
goto _start;
}
}
else
{
lean_object* v___x_1365_; 
lean_dec_ref(v_next_1354_);
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_a_1324_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1365_ = v___x_1344_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_snd_1342_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1365_);
v___x_1367_ = v___x_1351_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1344_);
lean_dec(v_snd_1342_);
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_a_1328_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_a_1324_);
v_a_1432_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1348_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1348_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1442_ = _args[0];
lean_object* v_a_1443_ = _args[1];
lean_object* v_a_1444_ = _args[2];
lean_object* v___x_1445_ = _args[3];
lean_object* v_a_1446_ = _args[4];
lean_object* v_e_1447_ = _args[5];
lean_object* v_a_1448_ = _args[6];
lean_object* v___y_1449_ = _args[7];
lean_object* v___y_1450_ = _args[8];
lean_object* v___y_1451_ = _args[9];
lean_object* v___y_1452_ = _args[10];
lean_object* v___y_1453_ = _args[11];
lean_object* v___y_1454_ = _args[12];
lean_object* v___y_1455_ = _args[13];
lean_object* v___y_1456_ = _args[14];
lean_object* v___y_1457_ = _args[15];
lean_object* v___y_1458_ = _args[16];
lean_object* v___y_1459_ = _args[17];
_start:
{
uint8_t v_a_111861__boxed_1460_; uint8_t v___x_111862__boxed_1461_; lean_object* v_res_1462_; 
v_a_111861__boxed_1460_ = lean_unbox(v_a_1444_);
v___x_111862__boxed_1461_ = lean_unbox(v___x_1445_);
v_res_1462_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1442_, v_a_1443_, v_a_111861__boxed_1460_, v___x_111862__boxed_1461_, v_a_1446_, v_e_1447_, v_a_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec(v___y_1449_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object* v_a_1463_, lean_object* v_a_1464_, uint8_t v_a_1465_, uint8_t v___x_1466_, lean_object* v_a_1467_, lean_object* v_e_1468_, lean_object* v_a_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_snd_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1579_; 
v_snd_1481_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_a_1469_, 0);
lean_dec(v_unused_1580_);
v___x_1483_ = v_a_1469_;
v_isShared_1484_ = v_isSharedCheck_1579_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_snd_1481_);
lean_dec(v_a_1469_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1579_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_st_ref_get(v___y_1470_);
lean_inc(v_snd_1481_);
v___x_1487_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1486_, v_snd_1481_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1570_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1570_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1570_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_self_1492_; lean_object* v_next_1493_; uint8_t v_ctor_1494_; 
v_self_1492_ = lean_ctor_get(v_a_1488_, 0);
lean_inc_ref(v_self_1492_);
v_next_1493_ = lean_ctor_get(v_a_1488_, 1);
lean_inc_ref(v_next_1493_);
v_ctor_1494_ = lean_ctor_get_uint8(v_a_1488_, sizeof(void*)*12 + 2);
lean_dec(v_a_1488_);
if (v_ctor_1494_ == 0)
{
lean_dec_ref(v_self_1492_);
goto v___jp_1495_;
}
else
{
lean_object* v_self_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_self_1509_ = lean_ctor_get(v_a_1464_, 0);
v___x_1510_ = l_Lean_Expr_getAppFn(v_self_1509_);
v___x_1511_ = l_Lean_Expr_getAppFn(v_self_1492_);
v___x_1512_ = lean_expr_eqv(v___x_1510_, v___x_1511_);
lean_dec_ref(v___x_1511_);
lean_dec_ref(v___x_1510_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_box(v_a_1465_);
v___x_1514_ = lean_box(v___x_1466_);
lean_inc_ref(v_self_1492_);
lean_inc_ref(v_a_1463_);
lean_inc_ref(v_a_1467_);
lean_inc_ref_n(v_self_1509_, 2);
v___f_1515_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1515_, 0, v___x_1513_);
lean_closure_set(v___f_1515_, 1, v___x_1514_);
lean_closure_set(v___f_1515_, 2, v_self_1509_);
lean_closure_set(v___f_1515_, 3, v_a_1467_);
lean_closure_set(v___f_1515_, 4, v_a_1463_);
lean_closure_set(v___f_1515_, 5, v_self_1492_);
v___x_1516_ = l_Lean_Meta_Grind_hasSameType(v_self_1509_, v_self_1492_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; uint8_t v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_unbox(v_a_1517_);
lean_dec(v_a_1517_);
if (v___x_1518_ == 0)
{
lean_dec_ref(v___f_1515_);
goto v___jp_1495_;
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref(v_next_1493_);
lean_del_object(v___x_1490_);
lean_del_object(v___x_1483_);
lean_dec_ref(v_a_1464_);
v___x_1519_ = l_Lean_Meta_mkEq(v_a_1467_, v_a_1463_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1));
v___x_1522_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1521_, v_a_1520_, v___f_1515_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4);
lean_inc_ref(v_e_1468_);
v___x_1525_ = l_Lean_mkAppB(v___x_1524_, v_e_1468_, v_a_1523_);
v___x_1526_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1468_, v___x_1525_, v___y_1470_, v___y_1472_, v___y_1474_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1536_; 
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v___x_1526_, 0);
lean_dec(v_unused_1537_);
v___x_1528_ = v___x_1526_;
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v___x_1526_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1530_ = lean_box(v___x_1466_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_snd_1481_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1532_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_snd_1481_);
v_a_1538_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1526_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1526_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_snd_1481_);
lean_dec_ref(v_e_1468_);
v_a_1546_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1522_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1522_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v___f_1515_);
lean_dec(v_snd_1481_);
lean_dec_ref(v_e_1468_);
v_a_1554_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1519_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1519_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v___f_1515_);
lean_dec_ref(v_next_1493_);
lean_del_object(v___x_1490_);
lean_del_object(v___x_1483_);
lean_dec(v_snd_1481_);
lean_dec_ref(v_e_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v_a_1463_);
v_a_1562_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1516_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1516_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_dec_ref(v_self_1492_);
goto v___jp_1495_;
}
}
v___jp_1495_:
{
size_t v___x_1496_; size_t v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_ptr_addr(v_next_1493_);
v___x_1497_ = lean_ptr_addr(v_a_1463_);
v___x_1498_ = lean_usize_dec_eq(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; 
lean_del_object(v___x_1490_);
lean_dec(v_snd_1481_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v_next_1493_);
lean_ctor_set(v___x_1483_, 0, v___x_1485_);
v___x_1500_ = v___x_1483_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_next_1493_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1463_, v_a_1464_, v_a_1465_, v___x_1466_, v_a_1467_, v_e_1468_, v___x_1500_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1501_;
}
}
else
{
lean_object* v___x_1504_; 
lean_dec_ref(v_next_1493_);
lean_dec_ref(v_e_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v_a_1463_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1485_);
v___x_1504_ = v___x_1483_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1481_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1504_);
v___x_1506_ = v___x_1490_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1483_);
lean_dec(v_snd_1481_);
lean_dec_ref(v_e_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_a_1464_);
lean_dec_ref(v_a_1463_);
v_a_1571_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1487_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1487_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_1581_ = _args[0];
lean_object* v_a_1582_ = _args[1];
lean_object* v_a_1583_ = _args[2];
lean_object* v___x_1584_ = _args[3];
lean_object* v_a_1585_ = _args[4];
lean_object* v_e_1586_ = _args[5];
lean_object* v_a_1587_ = _args[6];
lean_object* v___y_1588_ = _args[7];
lean_object* v___y_1589_ = _args[8];
lean_object* v___y_1590_ = _args[9];
lean_object* v___y_1591_ = _args[10];
lean_object* v___y_1592_ = _args[11];
lean_object* v___y_1593_ = _args[12];
lean_object* v___y_1594_ = _args[13];
lean_object* v___y_1595_ = _args[14];
lean_object* v___y_1596_ = _args[15];
lean_object* v___y_1597_ = _args[16];
lean_object* v___y_1598_ = _args[17];
_start:
{
uint8_t v_a_112118__boxed_1599_; uint8_t v___x_112119__boxed_1600_; lean_object* v_res_1601_; 
v_a_112118__boxed_1599_ = lean_unbox(v_a_1583_);
v___x_112119__boxed_1600_ = lean_unbox(v___x_1584_);
v_res_1601_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1581_, v_a_1582_, v_a_112118__boxed_1599_, v___x_112119__boxed_1600_, v_a_1585_, v_e_1586_, v_a_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec(v___y_1588_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(lean_object* v_a_1602_, lean_object* v_a_1603_, uint8_t v_a_1604_, uint8_t v___x_1605_, lean_object* v_e_1606_, lean_object* v_a_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_snd_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1676_; 
v_snd_1619_ = lean_ctor_get(v_a_1607_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_a_1607_, 0);
lean_dec(v_unused_1677_);
v___x_1621_ = v_a_1607_;
v_isShared_1622_ = v_isSharedCheck_1676_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_snd_1619_);
lean_dec(v_a_1607_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1676_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_st_ref_get(v___y_1608_);
lean_inc(v_snd_1619_);
v___x_1625_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1624_, v_snd_1619_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___x_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1667_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1667_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1667_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_next_1630_; uint8_t v_ctor_1631_; 
v_next_1630_ = lean_ctor_get(v_a_1626_, 1);
lean_inc_ref(v_next_1630_);
v_ctor_1631_ = lean_ctor_get_uint8(v_a_1626_, sizeof(void*)*12 + 2);
if (v_ctor_1631_ == 0)
{
lean_dec(v_a_1626_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_inc_ref_n(v_a_1603_, 2);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1623_);
lean_ctor_set(v___x_1646_, 1, v_a_1603_);
lean_inc_ref(v_e_1606_);
lean_inc_ref(v_a_1602_);
v___x_1647_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1603_, v_a_1626_, v_a_1604_, v___x_1605_, v_a_1602_, v_e_1606_, v___x_1646_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1666_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1666_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1666_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_fst_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1664_; 
v_fst_1652_ = lean_ctor_get(v_a_1648_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1648_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_a_1648_, 1);
lean_dec(v_unused_1665_);
v___x_1654_ = v_a_1648_;
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_fst_1652_);
lean_dec(v_a_1648_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1664_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
if (lean_obj_tag(v_fst_1652_) == 0)
{
lean_del_object(v___x_1654_);
lean_del_object(v___x_1650_);
goto v___jp_1632_;
}
else
{
lean_object* v_val_1656_; uint8_t v___x_1657_; 
v_val_1656_ = lean_ctor_get(v_fst_1652_, 0);
v___x_1657_ = lean_unbox(v_val_1656_);
if (v___x_1657_ == 0)
{
lean_dec_ref_known(v_fst_1652_, 1);
lean_del_object(v___x_1654_);
lean_del_object(v___x_1650_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v_next_1630_);
lean_del_object(v___x_1628_);
lean_del_object(v___x_1621_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_snd_1619_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_fst_1652_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_snd_1619_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1659_);
v___x_1661_ = v___x_1650_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_next_1630_);
lean_del_object(v___x_1628_);
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v___x_1647_;
}
}
v___jp_1632_:
{
size_t v___x_1633_; size_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_ptr_addr(v_next_1630_);
v___x_1634_ = lean_ptr_addr(v_a_1602_);
v___x_1635_ = lean_usize_dec_eq(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1637_; 
lean_del_object(v___x_1628_);
lean_dec(v_snd_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v_next_1630_);
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1637_ = v___x_1621_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_next_1630_);
v___x_1637_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v_a_1607_ = v___x_1637_;
goto _start;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec_ref(v_next_1630_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1641_ = v___x_1621_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_snd_1619_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1641_);
v___x_1643_ = v___x_1628_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1621_);
lean_dec(v_snd_1619_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
v_a_1668_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1625_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1625_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1678_ = _args[0];
lean_object* v_a_1679_ = _args[1];
lean_object* v_a_1680_ = _args[2];
lean_object* v___x_1681_ = _args[3];
lean_object* v_e_1682_ = _args[4];
lean_object* v_a_1683_ = _args[5];
lean_object* v___y_1684_ = _args[6];
lean_object* v___y_1685_ = _args[7];
lean_object* v___y_1686_ = _args[8];
lean_object* v___y_1687_ = _args[9];
lean_object* v___y_1688_ = _args[10];
lean_object* v___y_1689_ = _args[11];
lean_object* v___y_1690_ = _args[12];
lean_object* v___y_1691_ = _args[13];
lean_object* v___y_1692_ = _args[14];
lean_object* v___y_1693_ = _args[15];
lean_object* v___y_1694_ = _args[16];
_start:
{
uint8_t v_a_112361__boxed_1695_; uint8_t v___x_112362__boxed_1696_; lean_object* v_res_1697_; 
v_a_112361__boxed_1695_ = lean_unbox(v_a_1680_);
v___x_112362__boxed_1696_ = lean_unbox(v___x_1681_);
v_res_1697_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_1678_, v_a_1679_, v_a_112361__boxed_1695_, v___x_112362__boxed_1696_, v_e_1682_, v_a_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec(v___y_1684_);
return v_res_1697_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__6(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__5));
v___x_1712_ = l_Lean_mkConst(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__9(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_box(0);
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__8));
v___x_1720_ = l_Lean_mkConst(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__12(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__11));
v___x_1728_ = l_Lean_mkConst(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* v_e_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
lean_inc_ref(v_e_1729_);
v___x_1750_ = l_Lean_Expr_cleanupAnnotations(v_e_1729_);
v___x_1751_ = l_Lean_Expr_isApp(v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec_ref(v___x_1750_);
lean_dec_ref(v_e_1729_);
goto v___jp_1747_;
}
else
{
lean_object* v_arg_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_arg_1752_ = lean_ctor_get(v___x_1750_, 1);
lean_inc_ref(v_arg_1752_);
v___x_1753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1750_);
v___x_1754_ = l_Lean_Expr_isApp(v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1747_;
}
else
{
lean_object* v_arg_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_arg_1755_ = lean_ctor_get(v___x_1753_, 1);
lean_inc_ref(v_arg_1755_);
v___x_1756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1753_);
v___x_1757_ = l_Lean_Expr_isApp(v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1747_;
}
else
{
lean_object* v_arg_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_arg_1758_ = lean_ctor_get(v___x_1756_, 1);
lean_inc_ref(v_arg_1758_);
v___x_1759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1756_);
v___x_1760_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_1761_ = l_Lean_Expr_isConstOf(v___x_1759_, v___x_1760_);
lean_dec_ref(v___x_1759_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1747_;
}
else
{
lean_object* v___x_1762_; 
lean_inc_ref(v_arg_1755_);
v___x_1762_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1755_, v_a_1730_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
lean_inc_ref(v_arg_1752_);
v___x_1764_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1752_, v_a_1730_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v_self_1766_; uint8_t v_ctor_1767_; lean_object* v_self_1768_; uint8_t v_ctor_1769_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___x_1973_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v_self_1766_ = lean_ctor_get(v_a_1763_, 0);
lean_inc_ref(v_self_1766_);
v_ctor_1767_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*12 + 2);
lean_dec(v_a_1763_);
v_self_1768_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref(v_self_1768_);
v_ctor_1769_ = lean_ctor_get_uint8(v_a_1765_, sizeof(void*)*12 + 2);
lean_dec(v_a_1765_);
v___x_1973_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1734_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; size_t v___x_1975_; size_t v___x_1976_; uint8_t v___x_1977_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = lean_ptr_addr(v_self_1766_);
v___x_1976_ = lean_ptr_addr(v_a_1974_);
v___x_1977_ = lean_usize_dec_eq(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
size_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_ptr_addr(v_self_1768_);
v___x_1979_ = lean_usize_dec_eq(v___x_1978_, v___x_1976_);
if (v___x_1979_ == 0)
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_eq(v___x_1975_, v___x_1978_);
if (v___x_1980_ == 0)
{
lean_dec(v_a_1974_);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_st_ref_get(v_a_1730_);
lean_inc_ref(v_e_1729_);
v___x_1982_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1981_, v_e_1729_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v___x_1981_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; size_t v___x_1984_; uint8_t v___x_1985_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = lean_ptr_addr(v_a_1983_);
lean_dec(v_a_1983_);
v___x_1985_ = lean_usize_dec_eq(v___x_1984_, v___x_1976_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_inc(v_a_1739_);
lean_inc_ref(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
lean_inc_ref(v_a_1732_);
lean_inc(v_a_1731_);
lean_inc(v_a_1730_);
lean_inc_ref(v_arg_1752_);
lean_inc_ref(v_arg_1755_);
v___x_1986_ = lean_grind_mk_eq_proof(v_arg_1755_, v_arg_1752_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
lean_inc_ref_n(v_e_1729_, 2);
v___x_1988_ = l_Lean_Meta_mkEqTrueCore(v_e_1729_, v_a_1987_);
v___x_1989_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1729_, v_a_1974_, v___x_1988_, v___x_1985_, v_a_1730_, v_a_1732_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref_known(v___x_1989_, 1);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
else
{
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
return v___x_1989_;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v_a_1974_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1990_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1986_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1986_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_dec(v_a_1974_);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1974_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1998_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1982_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1982_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_st_ref_get(v_a_1730_);
lean_inc_ref(v_e_1729_);
v___x_2007_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2006_, v_e_1729_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v___x_2006_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; size_t v___x_2009_; uint8_t v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = lean_ptr_addr(v_a_2008_);
lean_dec(v_a_2008_);
v___x_2010_ = lean_usize_dec_eq(v___x_2009_, v___x_1975_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_inc(v_a_1739_);
lean_inc_ref(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
lean_inc_ref(v_a_1732_);
lean_inc(v_a_1731_);
lean_inc(v_a_1730_);
lean_inc_ref(v_arg_1752_);
v___x_2011_ = lean_grind_mk_eq_proof(v_arg_1752_, v_a_1974_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__9, &l_Lean_Meta_Grind_propagateEqUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__9);
lean_inc_ref(v_arg_1752_);
lean_inc_ref_n(v_arg_1755_, 2);
v___x_2014_ = l_Lean_mkApp3(v___x_2013_, v_arg_1755_, v_arg_1752_, v_a_2012_);
lean_inc_ref(v_e_1729_);
v___x_2015_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1729_, v_arg_1755_, v___x_2014_, v___x_2010_, v_a_1730_, v_a_1732_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref_known(v___x_2015_, 1);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
else
{
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
return v___x_2015_;
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2016_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2011_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2011_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_dec(v_a_1974_);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_1974_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2024_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2007_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2007_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_st_ref_get(v_a_1730_);
lean_inc_ref(v_e_1729_);
v___x_2033_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2032_, v_e_1729_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v___x_2032_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; size_t v___x_2035_; size_t v___x_2036_; uint8_t v___x_2037_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_ptr_addr(v_a_2034_);
lean_dec(v_a_2034_);
v___x_2036_ = lean_ptr_addr(v_self_1768_);
v___x_2037_ = lean_usize_dec_eq(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_inc(v_a_1739_);
lean_inc_ref(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_a_1736_);
lean_inc(v_a_1735_);
lean_inc_ref(v_a_1734_);
lean_inc(v_a_1733_);
lean_inc_ref(v_a_1732_);
lean_inc(v_a_1731_);
lean_inc(v_a_1730_);
lean_inc_ref(v_arg_1755_);
v___x_2038_ = lean_grind_mk_eq_proof(v_arg_1755_, v_a_1974_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__12, &l_Lean_Meta_Grind_propagateEqUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__12);
lean_inc_ref_n(v_arg_1752_, 2);
lean_inc_ref(v_arg_1755_);
v___x_2041_ = l_Lean_mkApp3(v___x_2040_, v_arg_1755_, v_arg_1752_, v_a_2039_);
lean_inc_ref(v_e_1729_);
v___x_2042_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1729_, v_arg_1752_, v___x_2041_, v___x_2037_, v_a_1730_, v_a_1732_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_dec_ref_known(v___x_2042_, 1);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
else
{
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
return v___x_2042_;
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2043_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2038_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2038_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_dec(v_a_1974_);
v___y_1819_ = v_a_1730_;
v___y_1820_ = v_a_1731_;
v___y_1821_ = v_a_1732_;
v___y_1822_ = v_a_1733_;
v___y_1823_ = v_a_1734_;
v___y_1824_ = v_a_1735_;
v___y_1825_ = v_a_1736_;
v___y_1826_ = v_a_1737_;
v___y_1827_ = v_a_1738_;
v___y_1828_ = v_a_1739_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_1974_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2051_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2033_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2033_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2059_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1973_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1973_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
v___jp_1770_:
{
size_t v___x_1784_; size_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_ptr_addr(v_self_1766_);
lean_dec_ref(v_self_1766_);
v___x_1785_ = lean_ptr_addr(v___y_1771_);
lean_dec_ref(v___y_1771_);
v___x_1786_ = lean_usize_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1744_;
}
else
{
size_t v___x_1787_; size_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1787_ = lean_ptr_addr(v_self_1768_);
lean_dec_ref(v_self_1768_);
v___x_1788_ = lean_ptr_addr(v___y_1776_);
lean_dec_ref(v___y_1776_);
v___x_1789_ = lean_usize_dec_eq(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1744_;
}
else
{
lean_object* v___x_1790_; 
lean_inc_ref(v_arg_1755_);
v___x_1790_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1755_, v___y_1780_, v___y_1774_, v___y_1781_, v___y_1773_, v___y_1783_, v___y_1775_, v___y_1782_, v___y_1779_, v___y_1778_, v___y_1777_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc_ref(v_arg_1752_);
v___x_1792_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1752_, v___y_1780_, v___y_1774_, v___y_1781_, v___y_1773_, v___y_1783_, v___y_1775_, v___y_1782_, v___y_1779_, v___y_1778_, v___y_1777_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1796_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
lean_inc_ref(v___y_1772_);
v___x_1797_ = l_Lean_Name_mkStr4(v___x_1794_, v___x_1795_, v___y_1772_, v___x_1796_);
v___x_1798_ = lean_box(0);
v___x_1799_ = l_Lean_mkConst(v___x_1797_, v___x_1798_);
v___x_1800_ = l_Lean_mkApp4(v___x_1799_, v_arg_1755_, v_arg_1752_, v_a_1791_, v_a_1793_);
v___x_1801_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1729_, v___x_1800_, v___y_1780_, v___y_1781_, v___y_1783_, v___y_1782_, v___y_1779_, v___y_1778_, v___y_1777_);
return v___x_1801_;
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1791_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1802_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1792_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1792_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1810_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1790_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1790_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
v___jp_1818_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__0));
v___x_1830_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
v___x_1831_ = l_Lean_Expr_isConstOf(v_arg_1758_, v___x_1830_);
lean_dec_ref(v_arg_1758_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_inc_ref(v_e_1729_);
v___x_1832_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1729_, v___y_1819_, v___y_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1903_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1903_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1903_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_unbox(v_a_1833_);
if (v___x_1837_ == 0)
{
lean_del_object(v___x_1835_);
if (v_ctor_1767_ == 0)
{
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1741_;
}
else
{
if (v_ctor_1769_ == 0)
{
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1741_;
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1838_ = l_Lean_Expr_getAppFn(v_self_1766_);
v___x_1839_ = l_Lean_Expr_getAppFn(v_self_1768_);
v___x_1840_ = lean_expr_eqv(v___x_1838_, v___x_1839_);
lean_dec_ref(v___x_1839_);
lean_dec_ref(v___x_1838_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_box(v___x_1761_);
lean_inc_ref(v_self_1768_);
lean_inc_ref(v_arg_1752_);
lean_inc_ref(v_arg_1755_);
lean_inc_ref(v_self_1766_);
lean_inc(v_a_1833_);
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1842_, 0, v_a_1833_);
lean_closure_set(v___f_1842_, 1, v___x_1841_);
lean_closure_set(v___f_1842_, 2, v_self_1766_);
lean_closure_set(v___f_1842_, 3, v_arg_1755_);
lean_closure_set(v___f_1842_, 4, v_arg_1752_);
lean_closure_set(v___f_1842_, 5, v_self_1768_);
v___x_1843_ = l_Lean_Meta_Grind_hasSameType(v_self_1766_, v_self_1768_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; uint8_t v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = lean_unbox(v_a_1844_);
lean_dec(v_a_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; 
lean_dec_ref(v___f_1842_);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_box(0);
lean_inc_ref(v_arg_1755_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_arg_1755_);
v___x_1849_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
v___x_1850_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_arg_1755_, v_arg_1752_, v___x_1849_, v___x_1761_, v_e_1729_, v___x_1848_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1858_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1846_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1846_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v___x_1867_; 
lean_dec(v_a_1833_);
v___x_1867_ = l_Lean_Meta_mkEq(v_arg_1755_, v_arg_1752_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1));
v___x_1870_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1869_, v_a_1868_, v___f_1842_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4);
lean_inc_ref(v_e_1729_);
v___x_1873_ = l_Lean_mkAppB(v___x_1872_, v_e_1729_, v_a_1871_);
v___x_1874_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1729_, v___x_1873_, v___y_1819_, v___y_1821_, v___y_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1874_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v_e_1729_);
v_a_1875_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1870_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1870_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec_ref(v___f_1842_);
lean_dec_ref(v_e_1729_);
v_a_1883_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1867_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1867_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v___f_1842_);
lean_dec(v_a_1833_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1891_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1843_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1843_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
goto v___jp_1741_;
}
}
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v_a_1833_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v___x_1899_ = lean_box(0);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1899_);
v___x_1901_ = v___x_1835_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1904_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1832_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1832_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___x_1912_; 
lean_inc_ref(v_e_1729_);
v___x_1912_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1729_, v___y_1819_, v___y_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; uint8_t v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_unbox(v_a_1913_);
lean_dec(v_a_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_1823_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_1823_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; size_t v___x_1919_; size_t v___x_1920_; uint8_t v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = lean_ptr_addr(v_self_1766_);
v___x_1920_ = lean_ptr_addr(v_a_1916_);
v___x_1921_ = lean_usize_dec_eq(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
v___y_1771_ = v_a_1918_;
v___y_1772_ = v___x_1829_;
v___y_1773_ = v___y_1822_;
v___y_1774_ = v___y_1820_;
v___y_1775_ = v___y_1824_;
v___y_1776_ = v_a_1916_;
v___y_1777_ = v___y_1828_;
v___y_1778_ = v___y_1827_;
v___y_1779_ = v___y_1826_;
v___y_1780_ = v___y_1819_;
v___y_1781_ = v___y_1821_;
v___y_1782_ = v___y_1825_;
v___y_1783_ = v___y_1823_;
goto v___jp_1770_;
}
else
{
size_t v___x_1922_; size_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = lean_ptr_addr(v_self_1768_);
v___x_1923_ = lean_ptr_addr(v_a_1918_);
v___x_1924_ = lean_usize_dec_eq(v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
v___y_1771_ = v_a_1918_;
v___y_1772_ = v___x_1829_;
v___y_1773_ = v___y_1822_;
v___y_1774_ = v___y_1820_;
v___y_1775_ = v___y_1824_;
v___y_1776_ = v_a_1916_;
v___y_1777_ = v___y_1828_;
v___y_1778_ = v___y_1827_;
v___y_1779_ = v___y_1826_;
v___y_1780_ = v___y_1819_;
v___y_1781_ = v___y_1821_;
v___y_1782_ = v___y_1825_;
v___y_1783_ = v___y_1823_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_a_1918_);
lean_dec(v_a_1916_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_inc_ref(v_arg_1755_);
v___x_1925_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1755_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
lean_inc_ref(v_arg_1752_);
v___x_1927_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1752_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__6, &l_Lean_Meta_Grind_propagateEqUp___closed__6_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__6);
v___x_1930_ = l_Lean_mkApp4(v___x_1929_, v_arg_1755_, v_arg_1752_, v_a_1926_, v_a_1928_);
v___x_1931_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1729_, v___x_1930_, v___y_1819_, v___y_1821_, v___y_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1931_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_a_1926_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1932_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1927_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1927_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1940_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1925_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1925_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_a_1916_);
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1948_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1917_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1917_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1956_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1915_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1915_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v___x_1964_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
v___x_1964_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_1729_, v_arg_1755_, v_arg_1752_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1964_;
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_self_1768_);
lean_dec_ref(v_self_1766_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_1965_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1912_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1912_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_a_1763_);
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2067_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1764_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1764_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v_arg_1758_);
lean_dec_ref(v_arg_1755_);
lean_dec_ref(v_arg_1752_);
lean_dec_ref(v_e_1729_);
v_a_2075_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_1762_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_1762_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
}
v___jp_1741_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
v___jp_1744_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
v___jp_1747_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object* v_e_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Meta_Grind_propagateEqUp(v_e_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec(v_a_2084_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object* v_00_u03b1_2096_, lean_object* v_name_2097_, uint8_t v_bi_2098_, lean_object* v_type_2099_, lean_object* v_k_2100_, uint8_t v_kind_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_2097_, v_bi_2098_, v_type_2099_, v_k_2100_, v_kind_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_2114_ = _args[0];
lean_object* v_name_2115_ = _args[1];
lean_object* v_bi_2116_ = _args[2];
lean_object* v_type_2117_ = _args[3];
lean_object* v_k_2118_ = _args[4];
lean_object* v_kind_2119_ = _args[5];
lean_object* v___y_2120_ = _args[6];
lean_object* v___y_2121_ = _args[7];
lean_object* v___y_2122_ = _args[8];
lean_object* v___y_2123_ = _args[9];
lean_object* v___y_2124_ = _args[10];
lean_object* v___y_2125_ = _args[11];
lean_object* v___y_2126_ = _args[12];
lean_object* v___y_2127_ = _args[13];
lean_object* v___y_2128_ = _args[14];
lean_object* v___y_2129_ = _args[15];
lean_object* v___y_2130_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2131_; uint8_t v_kind_boxed_2132_; lean_object* v_res_2133_; 
v_bi_boxed_2131_ = lean_unbox(v_bi_2116_);
v_kind_boxed_2132_ = lean_unbox(v_kind_2119_);
v_res_2133_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(v_00_u03b1_2114_, v_name_2115_, v_bi_boxed_2131_, v_type_2117_, v_k_2118_, v_kind_boxed_2132_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object* v_00_u03b1_2134_, lean_object* v_name_2135_, lean_object* v_type_2136_, lean_object* v_k_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_2135_, v_type_2136_, v_k_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object* v_00_u03b1_2150_, lean_object* v_name_2151_, lean_object* v_type_2152_, lean_object* v_k_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(v_00_u03b1_2150_, v_name_2151_, v_type_2152_, v_k_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec(v___y_2154_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object* v_a_2166_, lean_object* v_a_2167_, uint8_t v_a_2168_, uint8_t v___x_2169_, lean_object* v_a_2170_, lean_object* v_e_2171_, lean_object* v_inst_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_2166_, v_a_2167_, v_a_2168_, v___x_2169_, v_a_2170_, v_e_2171_, v_a_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object** _args){
lean_object* v_a_2186_ = _args[0];
lean_object* v_a_2187_ = _args[1];
lean_object* v_a_2188_ = _args[2];
lean_object* v___x_2189_ = _args[3];
lean_object* v_a_2190_ = _args[4];
lean_object* v_e_2191_ = _args[5];
lean_object* v_inst_2192_ = _args[6];
lean_object* v_a_2193_ = _args[7];
lean_object* v___y_2194_ = _args[8];
lean_object* v___y_2195_ = _args[9];
lean_object* v___y_2196_ = _args[10];
lean_object* v___y_2197_ = _args[11];
lean_object* v___y_2198_ = _args[12];
lean_object* v___y_2199_ = _args[13];
lean_object* v___y_2200_ = _args[14];
lean_object* v___y_2201_ = _args[15];
lean_object* v___y_2202_ = _args[16];
lean_object* v___y_2203_ = _args[17];
lean_object* v___y_2204_ = _args[18];
_start:
{
uint8_t v_a_113387__boxed_2205_; uint8_t v___x_113388__boxed_2206_; lean_object* v_res_2207_; 
v_a_113387__boxed_2205_ = lean_unbox(v_a_2188_);
v___x_113388__boxed_2206_ = lean_unbox(v___x_2189_);
v_res_2207_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(v_a_2186_, v_a_2187_, v_a_113387__boxed_2205_, v___x_113388__boxed_2206_, v_a_2190_, v_e_2191_, v_inst_2192_, v_a_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec(v___y_2194_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object* v_a_2208_, lean_object* v_a_2209_, uint8_t v_a_2210_, uint8_t v___x_2211_, lean_object* v_e_2212_, lean_object* v_inst_2213_, lean_object* v_a_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_2208_, v_a_2209_, v_a_2210_, v___x_2211_, v_e_2212_, v_a_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object** _args){
lean_object* v_a_2227_ = _args[0];
lean_object* v_a_2228_ = _args[1];
lean_object* v_a_2229_ = _args[2];
lean_object* v___x_2230_ = _args[3];
lean_object* v_e_2231_ = _args[4];
lean_object* v_inst_2232_ = _args[5];
lean_object* v_a_2233_ = _args[6];
lean_object* v___y_2234_ = _args[7];
lean_object* v___y_2235_ = _args[8];
lean_object* v___y_2236_ = _args[9];
lean_object* v___y_2237_ = _args[10];
lean_object* v___y_2238_ = _args[11];
lean_object* v___y_2239_ = _args[12];
lean_object* v___y_2240_ = _args[13];
lean_object* v___y_2241_ = _args[14];
lean_object* v___y_2242_ = _args[15];
lean_object* v___y_2243_ = _args[16];
lean_object* v___y_2244_ = _args[17];
_start:
{
uint8_t v_a_113440__boxed_2245_; uint8_t v___x_113441__boxed_2246_; lean_object* v_res_2247_; 
v_a_113440__boxed_2245_ = lean_unbox(v_a_2229_);
v___x_113441__boxed_2246_ = lean_unbox(v___x_2230_);
v_res_2247_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(v_a_2227_, v_a_2228_, v_a_113440__boxed_2245_, v___x_113441__boxed_2246_, v_e_2231_, v_inst_2232_, v_a_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec(v___y_2234_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object* v_a_2248_, lean_object* v_a_2249_, uint8_t v_a_2250_, uint8_t v___x_2251_, lean_object* v_a_2252_, lean_object* v_e_2253_, lean_object* v_inst_2254_, lean_object* v_a_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_2248_, v_a_2249_, v_a_2250_, v___x_2251_, v_a_2252_, v_e_2253_, v_a_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_a_2268_ = _args[0];
lean_object* v_a_2269_ = _args[1];
lean_object* v_a_2270_ = _args[2];
lean_object* v___x_2271_ = _args[3];
lean_object* v_a_2272_ = _args[4];
lean_object* v_e_2273_ = _args[5];
lean_object* v_inst_2274_ = _args[6];
lean_object* v_a_2275_ = _args[7];
lean_object* v___y_2276_ = _args[8];
lean_object* v___y_2277_ = _args[9];
lean_object* v___y_2278_ = _args[10];
lean_object* v___y_2279_ = _args[11];
lean_object* v___y_2280_ = _args[12];
lean_object* v___y_2281_ = _args[13];
lean_object* v___y_2282_ = _args[14];
lean_object* v___y_2283_ = _args[15];
lean_object* v___y_2284_ = _args[16];
lean_object* v___y_2285_ = _args[17];
lean_object* v___y_2286_ = _args[18];
_start:
{
uint8_t v_a_113490__boxed_2287_; uint8_t v___x_113491__boxed_2288_; lean_object* v_res_2289_; 
v_a_113490__boxed_2287_ = lean_unbox(v_a_2270_);
v___x_113491__boxed_2288_ = lean_unbox(v___x_2271_);
v_res_2289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(v_a_2268_, v_a_2269_, v_a_113490__boxed_2287_, v___x_113491__boxed_2288_, v_a_2272_, v_e_2273_, v_inst_2274_, v_a_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec(v___y_2276_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___boxed), 12, 0);
v___x_2293_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2291_, v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9____boxed(lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_();
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* v_e_2296_, lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_b_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_usize_dec_lt(v_i_2299_, v_sz_2298_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
lean_dec_ref(v_e_2296_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_b_2300_);
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; lean_object* v_a_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_box(0);
v_a_2315_ = lean_array_uget_borrowed(v_as_2297_, v_i_2299_);
lean_inc_ref(v_e_2296_);
lean_inc(v_a_2315_);
v___x_2316_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_a_2315_, v_e_2296_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2316_) == 0)
{
size_t v___x_2317_; size_t v___x_2318_; 
lean_dec_ref_known(v___x_2316_, 1);
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_add(v_i_2299_, v___x_2317_);
v_i_2299_ = v___x_2318_;
v_b_2300_ = v___x_2314_;
goto _start;
}
else
{
lean_dec_ref(v_e_2296_);
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* v_e_2320_, lean_object* v_as_2321_, lean_object* v_sz_2322_, lean_object* v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2322_);
lean_dec(v_sz_2322_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2323_);
lean_dec(v_i_2323_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2320_, v_as_2321_, v_sz_boxed_2336_, v_i_boxed_2337_, v_b_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v_as_2321_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* v_e_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2363_; 
lean_inc_ref(v_e_2342_);
v___x_2363_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2342_, v_a_2343_, v_a_2347_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; uint8_t v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = lean_unbox(v_a_2364_);
lean_dec(v_a_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
lean_inc_ref(v_e_2342_);
v___x_2366_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2342_, v_a_2343_, v_a_2347_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2481_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2481_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2481_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_unbox(v_a_2367_);
lean_dec(v_a_2367_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2374_; 
lean_dec_ref(v_e_2342_);
v___x_2372_ = lean_box(0);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
else
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
lean_del_object(v___x_2369_);
lean_inc_ref(v_e_2342_);
v___x_2376_ = l_Lean_Expr_cleanupAnnotations(v_e_2342_);
v___x_2377_ = l_Lean_Expr_isApp(v___x_2376_);
if (v___x_2377_ == 0)
{
lean_dec_ref(v___x_2376_);
lean_dec_ref(v_e_2342_);
goto v___jp_2354_;
}
else
{
lean_object* v_arg_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_arg_2378_ = lean_ctor_get(v___x_2376_, 1);
lean_inc_ref(v_arg_2378_);
v___x_2379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2376_);
v___x_2380_ = l_Lean_Expr_isApp(v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
goto v___jp_2354_;
}
else
{
lean_object* v_arg_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v_arg_2381_ = lean_ctor_get(v___x_2379_, 1);
lean_inc_ref(v_arg_2381_);
v___x_2382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2379_);
v___x_2383_ = l_Lean_Expr_isApp(v___x_2382_);
if (v___x_2383_ == 0)
{
lean_dec_ref(v___x_2382_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
goto v___jp_2354_;
}
else
{
lean_object* v_arg_2384_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_arg_2384_ = lean_ctor_get(v___x_2382_, 1);
lean_inc_ref(v_arg_2384_);
v___x_2475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2382_);
v___x_2476_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2477_ = l_Lean_Expr_isConstOf(v___x_2475_, v___x_2476_);
lean_dec_ref(v___x_2475_);
if (v___x_2477_ == 0)
{
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
goto v___jp_2354_;
}
else
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
v___x_2479_ = l_Lean_Expr_isConstOf(v_arg_2384_, v___x_2478_);
if (v___x_2479_ == 0)
{
v___y_2419_ = v_a_2343_;
v___y_2420_ = v_a_2344_;
v___y_2421_ = v_a_2345_;
v___y_2422_ = v_a_2346_;
v___y_2423_ = v_a_2347_;
v___y_2424_ = v_a_2348_;
v___y_2425_ = v_a_2349_;
v___y_2426_ = v_a_2350_;
v___y_2427_ = v_a_2351_;
v___y_2428_ = v_a_2352_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2480_; 
lean_inc_ref(v_arg_2378_);
lean_inc_ref(v_arg_2381_);
lean_inc_ref(v_e_2342_);
v___x_2480_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_2342_, v_arg_2381_, v_arg_2378_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_dec_ref_known(v___x_2480_, 1);
v___y_2419_ = v_a_2343_;
v___y_2420_ = v_a_2344_;
v___y_2421_ = v_a_2345_;
v___y_2422_ = v_a_2346_;
v___y_2423_ = v_a_2347_;
v___y_2424_ = v_a_2348_;
v___y_2425_ = v_a_2349_;
v___y_2426_ = v_a_2350_;
v___y_2427_ = v_a_2351_;
v___y_2428_ = v_a_2352_;
goto v___jp_2418_;
}
else
{
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
return v___x_2480_;
}
}
}
v___jp_2385_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2384_, v___y_2395_, v___y_2394_, v___y_2390_, v___y_2392_, v___y_2389_, v___y_2387_, v___y_2386_, v___y_2388_, v___y_2393_, v___y_2391_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; size_t v_sz_2399_; size_t v___x_2400_; lean_object* v___x_2401_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = lean_box(0);
v_sz_2399_ = lean_array_size(v_a_2397_);
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2342_, v_a_2397_, v_sz_2399_, v___x_2400_, v___x_2398_, v___y_2395_, v___y_2394_, v___y_2390_, v___y_2392_, v___y_2389_, v___y_2387_, v___y_2386_, v___y_2388_, v___y_2393_, v___y_2391_);
lean_dec(v_a_2397_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2409_);
v___x_2403_ = v___x_2401_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v___x_2401_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2398_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2398_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
return v___x_2401_;
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_e_2342_);
v_a_2410_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2396_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2396_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2429_; 
lean_inc_ref(v_arg_2378_);
lean_inc_ref(v_arg_2381_);
v___x_2429_ = l_Lean_Meta_Grind_Solvers_propagateDiseqs(v_arg_2381_, v_arg_2378_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref_known(v___x_2429_, 1);
lean_inc_ref(v_arg_2384_);
v___x_2430_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2384_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2466_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2466_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2466_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2435_ = lean_array_get_size(v_a_2431_);
lean_dec(v_a_2431_);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_nat_dec_eq(v___x_2435_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_del_object(v___x_2433_);
v___x_2438_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2381_, v___y_2419_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2378_, v___y_2419_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v___x_2442_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
v___x_2443_ = l_Lean_Expr_isAppOf(v_arg_2384_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_dec(v_a_2441_);
lean_dec(v_a_2439_);
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2424_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2423_;
v___y_2390_ = v___y_2421_;
v___y_2391_ = v___y_2428_;
v___y_2392_ = v___y_2422_;
v___y_2393_ = v___y_2427_;
v___y_2394_ = v___y_2420_;
v___y_2395_ = v___y_2419_;
goto v___jp_2385_;
}
else
{
uint8_t v_ctor_2444_; 
v_ctor_2444_ = lean_ctor_get_uint8(v_a_2439_, sizeof(void*)*12 + 2);
lean_dec(v_a_2439_);
if (v_ctor_2444_ == 0)
{
uint8_t v_ctor_2445_; 
v_ctor_2445_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*12 + 2);
lean_dec(v_a_2441_);
if (v_ctor_2445_ == 0)
{
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2424_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2423_;
v___y_2390_ = v___y_2421_;
v___y_2391_ = v___y_2428_;
v___y_2392_ = v___y_2422_;
v___y_2393_ = v___y_2427_;
v___y_2394_ = v___y_2420_;
v___y_2395_ = v___y_2419_;
goto v___jp_2385_;
}
else
{
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_e_2342_);
goto v___jp_2360_;
}
}
else
{
lean_dec(v_a_2441_);
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_e_2342_);
goto v___jp_2360_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_a_2439_);
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_e_2342_);
v_a_2446_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2440_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2440_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
v_a_2454_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2438_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2438_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
v___x_2462_ = lean_box(0);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2462_);
v___x_2464_ = v___x_2433_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
v_a_2467_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2430_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2430_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2384_);
lean_dec_ref(v_arg_2381_);
lean_dec_ref(v_arg_2378_);
lean_dec_ref(v_e_2342_);
return v___x_2429_;
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
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v_e_2342_);
v_a_2482_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2366_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2366_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v___x_2490_; uint8_t v___x_2491_; 
lean_inc_ref(v_e_2342_);
v___x_2490_ = l_Lean_Expr_cleanupAnnotations(v_e_2342_);
v___x_2491_ = l_Lean_Expr_isApp(v___x_2490_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v___x_2490_);
lean_dec_ref(v_e_2342_);
goto v___jp_2357_;
}
else
{
lean_object* v_arg_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_arg_2492_ = lean_ctor_get(v___x_2490_, 1);
lean_inc_ref(v_arg_2492_);
v___x_2493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2490_);
v___x_2494_ = l_Lean_Expr_isApp(v___x_2493_);
if (v___x_2494_ == 0)
{
lean_dec_ref(v___x_2493_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
goto v___jp_2357_;
}
else
{
lean_object* v_arg_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_arg_2495_ = lean_ctor_get(v___x_2493_, 1);
lean_inc_ref(v_arg_2495_);
v___x_2496_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2493_);
v___x_2497_ = l_Lean_Expr_isApp(v___x_2496_);
if (v___x_2497_ == 0)
{
lean_dec_ref(v___x_2496_);
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
goto v___jp_2357_;
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2498_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2496_);
v___x_2499_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2500_ = l_Lean_Expr_isConstOf(v___x_2498_, v___x_2499_);
lean_dec_ref(v___x_2498_);
if (v___x_2500_ == 0)
{
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
goto v___jp_2357_;
}
else
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2495_, v_arg_2492_, v_a_2343_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2524_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2524_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2524_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_unbox(v_a_2502_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; 
lean_del_object(v___x_2504_);
lean_inc_ref(v_e_2342_);
v___x_2507_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2342_, v_a_2508_);
v___x_2510_ = lean_unbox(v_a_2502_);
lean_dec(v_a_2502_);
v___x_2511_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2495_, v_arg_2492_, v___x_2509_, v___x_2510_, v_a_2343_, v_a_2345_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2511_;
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_a_2502_);
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
v_a_2512_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2507_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2507_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_dec(v_a_2502_);
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
v___x_2520_ = lean_box(0);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2520_);
v___x_2522_ = v___x_2504_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec_ref(v_arg_2495_);
lean_dec_ref(v_arg_2492_);
lean_dec_ref(v_e_2342_);
v_a_2525_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2501_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2501_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
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
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_e_2342_);
v_a_2533_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2363_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2363_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
v___jp_2354_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
v___jp_2357_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2360_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_box(0);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object* v_e_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_Grind_propagateEqDown(v_e_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec(v_a_2542_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2556_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown___boxed), 12, 0);
v___x_2557_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2555_, v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9____boxed(lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_();
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object* v_u_2563_, lean_object* v_00_u03b1_2564_, lean_object* v_binst_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1));
v___x_2572_ = l_Lean_mkConst(v___x_2571_, v_u_2563_);
v___x_2573_ = l_Lean_mkAppB(v___x_2572_, v_00_u03b1_2564_, v_binst_2565_);
v___x_2574_ = lean_box(0);
v___x_2575_ = l_Lean_Meta_synthInstance_x3f(v___x_2573_, v___x_2574_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object* v_u_2576_, lean_object* v_00_u03b1_2577_, lean_object* v_binst_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2576_, v_00_u03b1_2577_, v_binst_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object* v_u_2585_, lean_object* v_00_u03b1_2586_, lean_object* v_binst_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2585_, v_00_u03b1_2586_, v_binst_2587_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object* v_u_2600_, lean_object* v_00_u03b1_2601_, lean_object* v_binst_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(v_u_2600_, v_00_u03b1_2601_, v_binst_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec(v_a_2603_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* v_e_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
lean_inc_ref(v_e_2630_);
v___x_2645_ = l_Lean_Expr_cleanupAnnotations(v_e_2630_);
v___x_2646_ = l_Lean_Expr_isApp(v___x_2645_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v___x_2645_);
lean_dec_ref(v_e_2630_);
goto v___jp_2642_;
}
else
{
lean_object* v_arg_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v_arg_2647_ = lean_ctor_get(v___x_2645_, 1);
lean_inc_ref(v_arg_2647_);
v___x_2648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2645_);
v___x_2649_ = l_Lean_Expr_isApp(v___x_2648_);
if (v___x_2649_ == 0)
{
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
goto v___jp_2642_;
}
else
{
lean_object* v_arg_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_arg_2650_ = lean_ctor_get(v___x_2648_, 1);
lean_inc_ref(v_arg_2650_);
v___x_2651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2648_);
v___x_2652_ = l_Lean_Expr_isApp(v___x_2651_);
if (v___x_2652_ == 0)
{
lean_dec_ref(v___x_2651_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
goto v___jp_2642_;
}
else
{
lean_object* v_arg_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_arg_2653_ = lean_ctor_get(v___x_2651_, 1);
lean_inc_ref(v_arg_2653_);
v___x_2654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2651_);
v___x_2655_ = l_Lean_Expr_isApp(v___x_2654_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
goto v___jp_2642_;
}
else
{
lean_object* v_arg_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_arg_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc_ref(v_arg_2656_);
v___x_2657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2654_);
v___x_2658_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2659_ = l_Lean_Expr_isConstOf(v___x_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v___x_2657_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
goto v___jp_2642_;
}
else
{
lean_object* v_u_2660_; lean_object* v___x_2661_; 
v_u_2660_ = l_Lean_Expr_constLevels_x21(v___x_2657_);
lean_dec_ref(v___x_2657_);
v___x_2661_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2650_, v_arg_2647_, v_a_2631_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = lean_unbox(v_a_2662_);
lean_dec(v_a_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_inc_ref(v_arg_2647_);
lean_inc_ref(v_arg_2650_);
v___x_2664_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_arg_2650_, v_arg_2647_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2697_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2697_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2697_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
if (lean_obj_tag(v_a_2665_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_del_object(v___x_2667_);
v_val_2669_ = lean_ctor_get(v_a_2665_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_a_2665_, 1);
lean_inc_ref(v_arg_2653_);
lean_inc_ref(v_arg_2656_);
lean_inc(v_u_2660_);
v___x_2670_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2660_, v_arg_2656_, v_arg_2653_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2684_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2684_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2684_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
if (lean_obj_tag(v_a_2671_) == 1)
{
lean_object* v_val_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_del_object(v___x_2673_);
v_val_2675_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v_a_2671_, 1);
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
v___x_2677_ = l_Lean_mkConst(v___x_2676_, v_u_2660_);
v___x_2678_ = l_Lean_mkApp6(v___x_2677_, v_arg_2656_, v_arg_2653_, v_val_2675_, v_arg_2650_, v_arg_2647_, v_val_2669_);
v___x_2679_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_2630_, v___x_2678_, v_a_2631_, v_a_2633_, v_a_2635_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_dec(v_a_2671_);
lean_dec(v_val_2669_);
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v___x_2680_ = lean_box(0);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2680_);
v___x_2682_ = v___x_2673_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_val_2669_);
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v_a_2685_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2670_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2670_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec(v_a_2665_);
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v___x_2693_ = lean_box(0);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2693_);
v___x_2695_ = v___x_2667_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v_a_2698_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2664_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2664_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v___x_2706_; 
lean_inc_ref(v_arg_2653_);
lean_inc_ref(v_arg_2656_);
lean_inc(v_u_2660_);
v___x_2706_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2660_, v_arg_2656_, v_arg_2653_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2730_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2730_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
if (lean_obj_tag(v_a_2707_) == 1)
{
lean_object* v_val_2711_; lean_object* v___x_2712_; 
lean_del_object(v___x_2709_);
v_val_2711_ = lean_ctor_get(v_a_2707_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v_a_2707_, 1);
lean_inc(v_a_2640_);
lean_inc_ref(v_a_2639_);
lean_inc(v_a_2638_);
lean_inc_ref(v_a_2637_);
lean_inc(v_a_2636_);
lean_inc_ref(v_a_2635_);
lean_inc(v_a_2634_);
lean_inc_ref(v_a_2633_);
lean_inc(v_a_2632_);
lean_inc(v_a_2631_);
lean_inc_ref(v_arg_2647_);
lean_inc_ref(v_arg_2650_);
v___x_2712_ = lean_grind_mk_eq_proof(v_arg_2650_, v_arg_2647_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
v___x_2715_ = l_Lean_mkConst(v___x_2714_, v_u_2660_);
v___x_2716_ = l_Lean_mkApp6(v___x_2715_, v_arg_2656_, v_arg_2653_, v_val_2711_, v_arg_2650_, v_arg_2647_, v_a_2713_);
v___x_2717_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_2630_, v___x_2716_, v_a_2631_, v_a_2633_, v_a_2635_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
return v___x_2717_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_val_2711_);
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v_a_2718_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2712_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2712_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec(v_a_2707_);
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v___x_2726_ = lean_box(0);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2726_);
v___x_2728_ = v___x_2709_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v_a_2731_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2706_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2706_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_u_2660_);
lean_dec_ref(v_arg_2656_);
lean_dec_ref(v_arg_2653_);
lean_dec_ref(v_arg_2650_);
lean_dec_ref(v_arg_2647_);
lean_dec_ref(v_e_2630_);
v_a_2739_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2661_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2661_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
}
}
v___jp_2642_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object* v_e_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Meta_Grind_propagateBEqUp(v_e_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec(v_a_2748_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2762_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp___boxed), 12, 0);
v___x_2763_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2761_, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9____boxed(lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_();
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object* v_e_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
lean_inc_ref(v_e_2776_);
v___x_2791_ = l_Lean_Expr_cleanupAnnotations(v_e_2776_);
v___x_2792_ = l_Lean_Expr_isApp(v___x_2791_);
if (v___x_2792_ == 0)
{
lean_dec_ref(v___x_2791_);
lean_dec_ref(v_e_2776_);
goto v___jp_2788_;
}
else
{
lean_object* v_arg_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v_arg_2793_ = lean_ctor_get(v___x_2791_, 1);
lean_inc_ref(v_arg_2793_);
v___x_2794_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2791_);
v___x_2795_ = l_Lean_Expr_isApp(v___x_2794_);
if (v___x_2795_ == 0)
{
lean_dec_ref(v___x_2794_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
goto v___jp_2788_;
}
else
{
lean_object* v_arg_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_arg_2796_ = lean_ctor_get(v___x_2794_, 1);
lean_inc_ref(v_arg_2796_);
v___x_2797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2794_);
v___x_2798_ = l_Lean_Expr_isApp(v___x_2797_);
if (v___x_2798_ == 0)
{
lean_dec_ref(v___x_2797_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
goto v___jp_2788_;
}
else
{
lean_object* v_arg_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_arg_2799_ = lean_ctor_get(v___x_2797_, 1);
lean_inc_ref(v_arg_2799_);
v___x_2800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2797_);
v___x_2801_ = l_Lean_Expr_isApp(v___x_2800_);
if (v___x_2801_ == 0)
{
lean_dec_ref(v___x_2800_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
goto v___jp_2788_;
}
else
{
lean_object* v_arg_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_arg_2802_ = lean_ctor_get(v___x_2800_, 1);
lean_inc_ref(v_arg_2802_);
v___x_2803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2800_);
v___x_2804_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2805_ = l_Lean_Expr_isConstOf(v___x_2803_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_dec_ref(v___x_2803_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
goto v___jp_2788_;
}
else
{
lean_object* v___x_2806_; lean_object* v_u_2807_; lean_object* v___x_2808_; 
v___x_2806_ = lean_box(0);
v_u_2807_ = l_Lean_Expr_constLevels_x21(v___x_2803_);
lean_dec_ref(v___x_2803_);
lean_inc_ref(v_e_2776_);
v___x_2808_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_2776_, v_a_2777_, v_a_2781_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; uint8_t v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = lean_unbox(v_a_2809_);
lean_dec(v_a_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_inc_ref(v_e_2776_);
v___x_2811_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_2776_, v_a_2777_, v_a_2781_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2893_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2893_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2893_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v___x_2816_; 
v___x_2816_ = lean_unbox(v_a_2812_);
lean_dec(v_a_2812_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2819_; 
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v___x_2817_ = lean_box(0);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
else
{
lean_object* v___x_2821_; 
lean_del_object(v___x_2814_);
lean_inc_ref(v_arg_2799_);
lean_inc_ref(v_arg_2802_);
lean_inc(v_u_2807_);
v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2807_, v_arg_2802_, v_arg_2799_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2884_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2884_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2884_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
if (lean_obj_tag(v_a_2822_) == 1)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_del_object(v___x_2824_);
v_val_2826_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_a_2822_, 1);
v___x_2827_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2828_ = l_List_head_x21___redArg(v___x_2806_, v_u_2807_);
v___x_2829_ = l_Lean_Level_succ___override(v___x_2828_);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_mkConst(v___x_2827_, v___x_2831_);
lean_inc_ref(v_arg_2793_);
lean_inc_ref(v_arg_2796_);
lean_inc_ref(v_arg_2802_);
v___x_2833_ = l_Lean_mkApp3(v___x_2832_, v_arg_2802_, v_arg_2796_, v_arg_2793_);
v___x_2834_ = l_Lean_Meta_Sym_shareCommon(v___x_2833_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_2796_, v_a_2777_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = lean_box(0);
lean_inc(v_a_2786_);
lean_inc_ref(v_a_2785_);
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc(v_a_2835_);
v___x_2839_ = lean_grind_internalize(v_a_2835_, v_a_2837_, v___x_2838_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2840_; 
lean_dec_ref_known(v___x_2839_, 1);
v___x_2840_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2781_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2842_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
lean_inc(v_a_2786_);
lean_inc_ref(v_a_2785_);
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
lean_inc(v_a_2777_);
v___x_2842_ = lean_grind_mk_eq_proof(v_e_2776_, v_a_2841_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
v___x_2845_ = l_Lean_mkConst(v___x_2844_, v_u_2807_);
v___x_2846_ = l_Lean_mkApp6(v___x_2845_, v_arg_2802_, v_arg_2799_, v_val_2826_, v_arg_2796_, v_arg_2793_, v_a_2843_);
v___x_2847_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_2835_, v___x_2846_, v_a_2777_, v_a_2779_, v_a_2781_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2847_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2835_);
lean_dec(v_val_2826_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
v_a_2848_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2842_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2842_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2835_);
lean_dec(v_val_2826_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2856_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2840_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2840_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_dec(v_a_2835_);
lean_dec(v_val_2826_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
return v___x_2839_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2835_);
lean_dec(v_val_2826_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2864_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2836_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2836_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_val_2826_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2872_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2834_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2834_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
lean_dec(v_a_2822_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v___x_2880_ = lean_box(0);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2880_);
v___x_2882_ = v___x_2824_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2885_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2821_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2821_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2894_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2811_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2811_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v___x_2902_; 
lean_inc_ref(v_arg_2799_);
lean_inc_ref(v_arg_2802_);
lean_inc(v_u_2807_);
v___x_2902_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2807_, v_arg_2802_, v_arg_2799_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2937_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2937_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2937_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
if (lean_obj_tag(v_a_2903_) == 1)
{
lean_object* v_val_2907_; lean_object* v___x_2908_; 
lean_del_object(v___x_2905_);
v_val_2907_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_val_2907_);
lean_dec_ref_known(v_a_2903_, 1);
v___x_2908_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2781_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
lean_inc(v_a_2786_);
lean_inc_ref(v_a_2785_);
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
lean_inc(v_a_2777_);
v___x_2910_ = lean_grind_mk_eq_proof(v_e_2776_, v_a_2909_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
v___x_2913_ = l_Lean_mkConst(v___x_2912_, v_u_2807_);
lean_inc_ref(v_arg_2793_);
lean_inc_ref(v_arg_2796_);
v___x_2914_ = l_Lean_mkApp6(v___x_2913_, v_arg_2802_, v_arg_2799_, v_val_2907_, v_arg_2796_, v_arg_2793_, v_a_2911_);
v___x_2915_ = 0;
v___x_2916_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2796_, v_arg_2793_, v___x_2914_, v___x_2915_, v_a_2777_, v_a_2779_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_val_2907_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
v_a_2917_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2910_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2910_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_val_2907_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2925_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2908_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2908_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
lean_dec(v_a_2903_);
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v___x_2933_ = lean_box(0);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2933_);
v___x_2935_ = v___x_2905_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2938_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2902_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2902_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_u_2807_);
lean_dec_ref(v_arg_2802_);
lean_dec_ref(v_arg_2799_);
lean_dec_ref(v_arg_2796_);
lean_dec_ref(v_arg_2793_);
lean_dec_ref(v_e_2776_);
v_a_2946_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2808_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2808_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
}
}
}
v___jp_2788_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object* v_e_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Meta_Grind_propagateBEqDown(v_e_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec(v_a_2955_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2969_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqDown___boxed), 12, 0);
v___x_2970_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2968_, v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9____boxed(lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_();
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* v_e_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2993_; 
lean_inc_ref(v_e_2978_);
v___x_2993_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2978_, v_a_2979_, v_a_2983_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3031_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3031_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3031_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_unbox(v_a_2994_);
lean_dec(v_a_2994_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_dec_ref(v_e_2978_);
v___x_2999_ = lean_box(0);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2999_);
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
else
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
lean_del_object(v___x_2996_);
lean_inc_ref(v_e_2978_);
v___x_3003_ = l_Lean_Expr_cleanupAnnotations(v_e_2978_);
v___x_3004_ = l_Lean_Expr_isApp(v___x_3003_);
if (v___x_3004_ == 0)
{
lean_dec_ref(v___x_3003_);
lean_dec_ref(v_e_2978_);
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_arg_3005_ = lean_ctor_get(v___x_3003_, 1);
lean_inc_ref(v_arg_3005_);
v___x_3006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3003_);
v___x_3007_ = l_Lean_Expr_isApp(v___x_3006_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3006_);
lean_dec_ref(v_arg_3005_);
lean_dec_ref(v_e_2978_);
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_arg_3008_ = lean_ctor_get(v___x_3006_, 1);
lean_inc_ref(v_arg_3008_);
v___x_3009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3006_);
v___x_3010_ = l_Lean_Expr_isApp(v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec_ref(v___x_3009_);
lean_dec_ref(v_arg_3008_);
lean_dec_ref(v_arg_3005_);
lean_dec_ref(v_e_2978_);
goto v___jp_2990_;
}
else
{
lean_object* v_arg_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_arg_3011_ = lean_ctor_get(v___x_3009_, 1);
lean_inc_ref(v_arg_3011_);
v___x_3012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3009_);
v___x_3013_ = l_Lean_Expr_isApp(v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3012_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_arg_3008_);
lean_dec_ref(v_arg_3005_);
lean_dec_ref(v_e_2978_);
goto v___jp_2990_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3012_);
v___x_3015_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3016_ = l_Lean_Expr_isConstOf(v___x_3014_, v___x_3015_);
lean_dec_ref(v___x_3014_);
if (v___x_3016_ == 0)
{
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_arg_3008_);
lean_dec_ref(v_arg_3005_);
lean_dec_ref(v_e_2978_);
goto v___jp_2990_;
}
else
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_arg_3005_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3017_, 1);
lean_inc_ref(v_e_2978_);
v___x_3018_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2978_, v_a_3019_);
v___x_3021_ = 0;
v___x_3022_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3011_, v_arg_3008_, v___x_3020_, v___x_3021_, v_a_2979_, v_a_2981_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
return v___x_3022_;
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_arg_3008_);
lean_dec_ref(v_e_2978_);
v_a_3023_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3018_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3018_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_arg_3008_);
lean_dec_ref(v_e_2978_);
return v___x_3017_;
}
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
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_e_2978_);
v_a_3032_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2993_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2993_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object* v_e_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_Meta_Grind_propagateEqMatchDown(v_e_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec(v_a_3041_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3055_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown___boxed), 12, 0);
v___x_3056_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3054_, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9____boxed(lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_();
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* v_e_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3077_; 
lean_inc_ref(v_e_3062_);
v___x_3077_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3062_, v_a_3063_, v_a_3067_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3113_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3113_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3113_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_unbox(v_a_3078_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
v___x_3083_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3083_);
v___x_3085_ = v___x_3080_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
else
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
lean_del_object(v___x_3080_);
lean_inc_ref(v_e_3062_);
v___x_3087_ = l_Lean_Expr_cleanupAnnotations(v_e_3062_);
v___x_3088_ = l_Lean_Expr_isApp(v___x_3087_);
if (v___x_3088_ == 0)
{
lean_dec_ref(v___x_3087_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
goto v___jp_3074_;
}
else
{
lean_object* v_arg_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v_arg_3089_ = lean_ctor_get(v___x_3087_, 1);
lean_inc_ref(v_arg_3089_);
v___x_3090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3087_);
v___x_3091_ = l_Lean_Expr_isApp(v___x_3090_);
if (v___x_3091_ == 0)
{
lean_dec_ref(v___x_3090_);
lean_dec_ref(v_arg_3089_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
goto v___jp_3074_;
}
else
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3090_);
v___x_3093_ = l_Lean_Expr_isApp(v___x_3092_);
if (v___x_3093_ == 0)
{
lean_dec_ref(v___x_3092_);
lean_dec_ref(v_arg_3089_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
goto v___jp_3074_;
}
else
{
lean_object* v_arg_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_arg_3094_ = lean_ctor_get(v___x_3092_, 1);
lean_inc_ref(v_arg_3094_);
v___x_3095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3092_);
v___x_3096_ = l_Lean_Expr_isApp(v___x_3095_);
if (v___x_3096_ == 0)
{
lean_dec_ref(v___x_3095_);
lean_dec_ref(v_arg_3094_);
lean_dec_ref(v_arg_3089_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
goto v___jp_3074_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3095_);
v___x_3098_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3099_ = l_Lean_Expr_isConstOf(v___x_3097_, v___x_3098_);
lean_dec_ref(v___x_3097_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v_arg_3094_);
lean_dec_ref(v_arg_3089_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
goto v___jp_3074_;
}
else
{
lean_object* v___x_3100_; 
lean_inc_ref(v_e_3062_);
v___x_3100_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3062_, v_a_3101_);
v___x_3103_ = lean_unbox(v_a_3078_);
lean_dec(v_a_3078_);
v___x_3104_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3094_, v_arg_3089_, v___x_3102_, v___x_3103_, v_a_3063_, v_a_3065_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3104_;
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v_arg_3094_);
lean_dec_ref(v_arg_3089_);
lean_dec(v_a_3078_);
lean_dec_ref(v_e_3062_);
v_a_3105_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3100_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3100_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
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
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v_e_3062_);
v_a_3114_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3077_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3077_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
v___jp_3074_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object* v_e_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Meta_Grind_propagateHEqDown(v_e_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec(v_a_3123_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3137_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown___boxed), 12, 0);
v___x_3138_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3136_, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9____boxed(lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_();
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* v_e_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
lean_inc_ref(v_e_3141_);
v___x_3156_ = l_Lean_Expr_cleanupAnnotations(v_e_3141_);
v___x_3157_ = l_Lean_Expr_isApp(v___x_3156_);
if (v___x_3157_ == 0)
{
lean_dec_ref(v___x_3156_);
lean_dec_ref(v_e_3141_);
goto v___jp_3153_;
}
else
{
lean_object* v_arg_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_arg_3158_ = lean_ctor_get(v___x_3156_, 1);
lean_inc_ref(v_arg_3158_);
v___x_3159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3156_);
v___x_3160_ = l_Lean_Expr_isApp(v___x_3159_);
if (v___x_3160_ == 0)
{
lean_dec_ref(v___x_3159_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
goto v___jp_3153_;
}
else
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3159_);
v___x_3162_ = l_Lean_Expr_isApp(v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec_ref(v___x_3161_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
goto v___jp_3153_;
}
else
{
lean_object* v_arg_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_arg_3163_ = lean_ctor_get(v___x_3161_, 1);
lean_inc_ref(v_arg_3163_);
v___x_3164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3161_);
v___x_3165_ = l_Lean_Expr_isApp(v___x_3164_);
if (v___x_3165_ == 0)
{
lean_dec_ref(v___x_3164_);
lean_dec_ref(v_arg_3163_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
goto v___jp_3153_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3164_);
v___x_3167_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3168_ = l_Lean_Expr_isConstOf(v___x_3166_, v___x_3167_);
lean_dec_ref(v___x_3166_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_arg_3163_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
goto v___jp_3153_;
}
else
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_3163_, v_arg_3158_, v_a_3142_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3191_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3191_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_unbox(v_a_3170_);
lean_dec(v_a_3170_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
lean_dec_ref(v_arg_3163_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
v___x_3175_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3175_);
v___x_3177_ = v___x_3172_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
else
{
lean_object* v___x_3179_; 
lean_del_object(v___x_3172_);
lean_inc(v_a_3151_);
lean_inc_ref(v_a_3150_);
lean_inc(v_a_3149_);
lean_inc_ref(v_a_3148_);
lean_inc(v_a_3147_);
lean_inc_ref(v_a_3146_);
lean_inc(v_a_3145_);
lean_inc_ref(v_a_3144_);
lean_inc(v_a_3143_);
lean_inc(v_a_3142_);
v___x_3179_ = lean_grind_mk_heq_proof(v_arg_3163_, v_arg_3158_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
lean_inc_ref(v_e_3141_);
v___x_3181_ = l_Lean_Meta_mkEqTrueCore(v_e_3141_, v_a_3180_);
v___x_3182_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3141_, v___x_3181_, v_a_3142_, v_a_3144_, v_a_3146_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3182_;
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v_e_3141_);
v_a_3183_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3179_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3179_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v_arg_3163_);
lean_dec_ref(v_arg_3158_);
lean_dec_ref(v_e_3141_);
v_a_3192_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3169_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3169_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
}
}
v___jp_3153_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object* v_e_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Meta_Grind_propagateHEqUp(v_e_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec(v_a_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp___boxed), 12, 0);
v___x_3216_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3214_, v___x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9____boxed(lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_();
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object* v_e_3219_, lean_object* v_args_3220_, uint8_t v_ite_3221_, lean_object* v_rhs_3222_, lean_object* v_h_3223_, lean_object* v_i_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = lean_array_get_size(v_args_3220_);
v___x_3237_ = lean_nat_dec_lt(v_i_3224_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
lean_dec(v_i_3224_);
v___x_3238_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_rhs_3222_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3219_, v_a_3225_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
lean_inc_ref(v_e_3219_);
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_e_3219_);
lean_inc(v_a_3234_);
lean_inc_ref(v_a_3233_);
lean_inc(v_a_3232_);
lean_inc_ref(v_a_3231_);
lean_inc(v_a_3230_);
lean_inc_ref(v_a_3229_);
lean_inc(v_a_3228_);
lean_inc_ref(v_a_3227_);
lean_inc(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc(v_a_3239_);
v___x_3243_ = lean_grind_internalize(v_a_3239_, v_a_3241_, v___x_3242_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_dec_ref_known(v___x_3243_, 1);
if (v_ite_3221_ == 0)
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3219_, v_a_3239_, v_h_3223_, v___x_3237_, v_a_3225_, v_a_3227_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
return v___x_3244_;
}
else
{
lean_object* v___x_3245_; 
lean_inc(v_a_3239_);
lean_inc_ref(v_e_3219_);
v___x_3245_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3219_, v_a_3239_, v_a_3225_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref_known(v___x_3245_, 1);
v___x_3246_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3219_, v_a_3239_, v_h_3223_, v___x_3237_, v_a_3225_, v_a_3227_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
return v___x_3246_;
}
else
{
lean_dec(v_a_3239_);
lean_dec_ref(v_h_3223_);
lean_dec_ref(v_e_3219_);
return v___x_3245_;
}
}
}
else
{
lean_dec(v_a_3239_);
lean_dec_ref(v_h_3223_);
lean_dec_ref(v_e_3219_);
return v___x_3243_;
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_a_3239_);
lean_dec_ref(v_h_3223_);
lean_dec_ref(v_e_3219_);
v_a_3247_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3240_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3240_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_h_3223_);
lean_dec_ref(v_e_3219_);
v_a_3255_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3238_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3238_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_arg_3263_; lean_object* v_rhs_x27_3264_; lean_object* v___x_3265_; 
v_arg_3263_ = lean_array_fget_borrowed(v_args_3220_, v_i_3224_);
lean_inc_n(v_arg_3263_, 2);
v_rhs_x27_3264_ = l_Lean_Expr_app___override(v_rhs_3222_, v_arg_3263_);
v___x_3265_ = l_Lean_Meta_mkCongrFun(v_h_3223_, v_arg_3263_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_unsigned_to_nat(1u);
v___x_3268_ = lean_nat_add(v_i_3224_, v___x_3267_);
lean_dec(v_i_3224_);
v_rhs_3222_ = v_rhs_x27_3264_;
v_h_3223_ = v_a_3266_;
v_i_3224_ = v___x_3268_;
goto _start;
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_rhs_x27_3264_);
lean_dec(v_i_3224_);
lean_dec_ref(v_e_3219_);
v_a_3270_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3265_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3265_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object** _args){
lean_object* v_e_3278_ = _args[0];
lean_object* v_args_3279_ = _args[1];
lean_object* v_ite_3280_ = _args[2];
lean_object* v_rhs_3281_ = _args[3];
lean_object* v_h_3282_ = _args[4];
lean_object* v_i_3283_ = _args[5];
lean_object* v_a_3284_ = _args[6];
lean_object* v_a_3285_ = _args[7];
lean_object* v_a_3286_ = _args[8];
lean_object* v_a_3287_ = _args[9];
lean_object* v_a_3288_ = _args[10];
lean_object* v_a_3289_ = _args[11];
lean_object* v_a_3290_ = _args[12];
lean_object* v_a_3291_ = _args[13];
lean_object* v_a_3292_ = _args[14];
lean_object* v_a_3293_ = _args[15];
lean_object* v_a_3294_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3295_; lean_object* v_res_3296_; 
v_ite_boxed_3295_ = lean_unbox(v_ite_3280_);
v_res_3296_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3278_, v_args_3279_, v_ite_boxed_3295_, v_rhs_3281_, v_h_3282_, v_i_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec_ref(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_a_3288_);
lean_dec(v_a_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_args_3279_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object* v_e_3297_, lean_object* v_rhs_3298_, lean_object* v_h_3299_, lean_object* v_prefixSize_3300_, lean_object* v_args_3301_, uint8_t v_ite_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3323_ = lean_array_get_size(v_args_3301_);
v___x_3324_ = lean_nat_dec_eq(v_prefixSize_3300_, v___x_3323_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; 
v___x_3325_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3297_, v_args_3301_, v_ite_3302_, v_rhs_3298_, v_h_3299_, v_prefixSize_3300_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; 
lean_dec(v_prefixSize_3300_);
v___x_3326_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3297_, v_a_3303_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
lean_inc_ref(v_e_3297_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_e_3297_);
lean_inc(v_a_3312_);
lean_inc_ref(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc_ref(v_a_3309_);
lean_inc(v_a_3308_);
lean_inc_ref(v_a_3307_);
lean_inc(v_a_3306_);
lean_inc_ref(v_a_3305_);
lean_inc(v_a_3304_);
lean_inc(v_a_3303_);
lean_inc_ref(v_rhs_3298_);
v___x_3329_ = lean_grind_internalize(v_rhs_3298_, v_a_3327_, v___x_3328_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_dec_ref_known(v___x_3329_, 1);
if (v_ite_3302_ == 0)
{
v___y_3315_ = v_a_3303_;
v___y_3316_ = v_a_3305_;
v___y_3317_ = v_a_3309_;
v___y_3318_ = v_a_3310_;
v___y_3319_ = v_a_3311_;
v___y_3320_ = v_a_3312_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3330_; 
lean_inc_ref(v_rhs_3298_);
lean_inc_ref(v_e_3297_);
v___x_3330_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3297_, v_rhs_3298_, v_a_3303_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_dec_ref_known(v___x_3330_, 1);
v___y_3315_ = v_a_3303_;
v___y_3316_ = v_a_3305_;
v___y_3317_ = v_a_3309_;
v___y_3318_ = v_a_3310_;
v___y_3319_ = v_a_3311_;
v___y_3320_ = v_a_3312_;
goto v___jp_3314_;
}
else
{
lean_dec_ref(v_h_3299_);
lean_dec_ref(v_rhs_3298_);
lean_dec_ref(v_e_3297_);
return v___x_3330_;
}
}
}
else
{
lean_dec_ref(v_h_3299_);
lean_dec_ref(v_rhs_3298_);
lean_dec_ref(v_e_3297_);
return v___x_3329_;
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_h_3299_);
lean_dec_ref(v_rhs_3298_);
lean_dec_ref(v_e_3297_);
v_a_3331_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3326_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3326_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
v___jp_3314_:
{
uint8_t v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = 0;
v___x_3322_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3297_, v_rhs_3298_, v_h_3299_, v___x_3321_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object** _args){
lean_object* v_e_3339_ = _args[0];
lean_object* v_rhs_3340_ = _args[1];
lean_object* v_h_3341_ = _args[2];
lean_object* v_prefixSize_3342_ = _args[3];
lean_object* v_args_3343_ = _args[4];
lean_object* v_ite_3344_ = _args[5];
lean_object* v_a_3345_ = _args[6];
lean_object* v_a_3346_ = _args[7];
lean_object* v_a_3347_ = _args[8];
lean_object* v_a_3348_ = _args[9];
lean_object* v_a_3349_ = _args[10];
lean_object* v_a_3350_ = _args[11];
lean_object* v_a_3351_ = _args[12];
lean_object* v_a_3352_ = _args[13];
lean_object* v_a_3353_ = _args[14];
lean_object* v_a_3354_ = _args[15];
lean_object* v_a_3355_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3356_; lean_object* v_res_3357_; 
v_ite_boxed_3356_ = lean_unbox(v_ite_3344_);
v_res_3357_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3339_, v_rhs_3340_, v_h_3341_, v_prefixSize_3342_, v_args_3343_, v_ite_boxed_3356_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_args_3343_);
return v_res_3357_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateIte___closed__0(void){
_start:
{
lean_object* v___x_3358_; lean_object* v_dummy_3359_; 
v___x_3358_ = lean_box(0);
v_dummy_3359_ = l_Lean_Expr_sort___override(v___x_3358_);
return v_dummy_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* v_e_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_numArgs_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_numArgs_3378_ = l_Lean_Expr_getAppNumArgs(v_e_3366_);
v___x_3379_ = lean_unsigned_to_nat(5u);
v___x_3380_ = lean_nat_dec_lt(v_numArgs_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v_c_3385_; lean_object* v___x_3386_; 
v___x_3381_ = l_Lean_instInhabitedExpr;
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_nat_sub(v_numArgs_3378_, v___x_3382_);
v___x_3384_ = lean_nat_sub(v___x_3383_, v___x_3382_);
v_c_3385_ = l_Lean_Expr_getRevArg_x21(v_e_3366_, v___x_3384_);
lean_inc_ref(v_c_3385_);
v___x_3386_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3385_, v_a_3367_, v_a_3371_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; uint8_t v___x_3388_; uint8_t v___x_3389_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = 1;
v___x_3389_ = lean_unbox(v_a_3387_);
lean_dec(v_a_3387_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_inc_ref(v_c_3385_);
v___x_3390_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3385_, v_a_3367_, v_a_3371_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3423_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3423_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3423_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_unbox(v_a_3391_);
lean_dec(v_a_3391_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3398_; 
lean_dec_ref(v_c_3385_);
lean_dec(v___x_3383_);
lean_dec(v_numArgs_3378_);
lean_dec_ref(v_e_3366_);
v___x_3396_ = lean_box(0);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3396_);
v___x_3398_ = v___x_3393_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
else
{
lean_object* v___x_3400_; lean_object* v_dummy_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_del_object(v___x_3393_);
v___x_3400_ = l_Lean_Expr_getAppFn(v_e_3366_);
v_dummy_3401_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3402_ = lean_mk_array(v_numArgs_3378_, v_dummy_3401_);
lean_inc_ref(v_e_3366_);
v___x_3403_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3366_, v___x_3402_, v___x_3383_);
v___x_3404_ = lean_unsigned_to_nat(4u);
v___x_3405_ = lean_array_get(v___x_3381_, v___x_3403_, v___x_3404_);
v___x_3406_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3385_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3406_, 1);
v___x_3408_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
v___x_3409_ = l_Lean_Expr_constLevels_x21(v___x_3400_);
lean_dec_ref(v___x_3400_);
v___x_3410_ = l_Lean_mkConst(v___x_3408_, v___x_3409_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = l_Lean_mkAppRange(v___x_3410_, v___x_3411_, v___x_3379_, v___x_3403_);
v___x_3413_ = l_Lean_Expr_app___override(v___x_3412_, v_a_3407_);
v___x_3414_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3366_, v___x_3405_, v___x_3413_, v___x_3379_, v___x_3403_, v___x_3388_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec_ref(v___x_3403_);
return v___x_3414_;
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v___x_3405_);
lean_dec_ref(v___x_3403_);
lean_dec_ref(v___x_3400_);
lean_dec_ref(v_e_3366_);
v_a_3415_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3406_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3406_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_c_3385_);
lean_dec(v___x_3383_);
lean_dec(v_numArgs_3378_);
lean_dec_ref(v_e_3366_);
v_a_3424_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3390_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3390_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
lean_object* v___x_3432_; lean_object* v_dummy_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3432_ = l_Lean_Expr_getAppFn(v_e_3366_);
v_dummy_3433_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3434_ = lean_mk_array(v_numArgs_3378_, v_dummy_3433_);
lean_inc_ref(v_e_3366_);
v___x_3435_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3366_, v___x_3434_, v___x_3383_);
v___x_3436_ = lean_unsigned_to_nat(3u);
v___x_3437_ = lean_array_get(v___x_3381_, v___x_3435_, v___x_3436_);
v___x_3438_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3385_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__4));
v___x_3441_ = l_Lean_Expr_constLevels_x21(v___x_3432_);
lean_dec_ref(v___x_3432_);
v___x_3442_ = l_Lean_mkConst(v___x_3440_, v___x_3441_);
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = l_Lean_mkAppRange(v___x_3442_, v___x_3443_, v___x_3379_, v___x_3435_);
v___x_3445_ = l_Lean_Expr_app___override(v___x_3444_, v_a_3439_);
v___x_3446_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3366_, v___x_3437_, v___x_3445_, v___x_3379_, v___x_3435_, v___x_3388_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
lean_dec_ref(v___x_3435_);
return v___x_3446_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___x_3437_);
lean_dec_ref(v___x_3435_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_e_3366_);
v_a_3447_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3438_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3438_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec_ref(v_c_3385_);
lean_dec(v___x_3383_);
lean_dec(v_numArgs_3378_);
lean_dec_ref(v_e_3366_);
v_a_3455_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3386_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3386_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec(v_numArgs_3378_);
lean_dec_ref(v_e_3366_);
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object* v_e_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Meta_Grind_propagateIte(v_e_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
lean_dec(v_a_3467_);
lean_dec(v_a_3466_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_));
v___x_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte___boxed), 12, 0);
v___x_3484_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3482_, v___x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9____boxed(lean_object* v_a_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_();
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* v_e_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v_numArgs_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_numArgs_3509_ = l_Lean_Expr_getAppNumArgs(v_e_3497_);
v___x_3510_ = lean_unsigned_to_nat(5u);
v___x_3511_ = lean_nat_dec_lt(v_numArgs_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v_c_3516_; lean_object* v___x_3517_; 
v___x_3512_ = l_Lean_instInhabitedExpr;
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = lean_nat_sub(v_numArgs_3509_, v___x_3513_);
v___x_3515_ = lean_nat_sub(v___x_3514_, v___x_3513_);
v_c_3516_ = l_Lean_Expr_getRevArg_x21(v_e_3497_, v___x_3515_);
lean_inc_ref(v_c_3516_);
v___x_3517_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3516_, v_a_3498_, v_a_3502_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; uint8_t v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = lean_unbox(v_a_3518_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_inc_ref(v_c_3516_);
v___x_3520_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3516_, v_a_3498_, v_a_3502_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3577_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3577_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3577_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_unbox(v_a_3521_);
lean_dec(v_a_3521_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
lean_dec(v_a_3518_);
lean_dec_ref(v_c_3516_);
lean_dec(v___x_3514_);
lean_dec(v_numArgs_3509_);
lean_dec_ref(v_e_3497_);
v___x_3526_ = lean_box(0);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3526_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
else
{
lean_object* v___x_3530_; lean_object* v_dummy_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_del_object(v___x_3523_);
v___x_3530_ = l_Lean_Expr_getAppFn(v_e_3497_);
v_dummy_3531_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3532_ = lean_mk_array(v_numArgs_3509_, v_dummy_3531_);
lean_inc_ref(v_e_3497_);
v___x_3533_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3497_, v___x_3532_, v___x_3514_);
lean_inc_ref(v_c_3516_);
v___x_3534_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3516_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_n(v_a_3535_, 2);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = lean_unsigned_to_nat(4u);
v___x_3537_ = lean_array_get_borrowed(v___x_3512_, v___x_3533_, v___x_3536_);
v___x_3538_ = l_Lean_Meta_mkOfEqFalseCore(v_c_3516_, v_a_3535_);
lean_inc(v___x_3537_);
v___x_3539_ = l_Lean_Expr_app___override(v___x_3537_, v___x_3538_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_a_3503_);
lean_inc_ref(v_a_3502_);
lean_inc(v_a_3501_);
lean_inc_ref(v_a_3500_);
lean_inc(v_a_3499_);
lean_inc(v_a_3498_);
v___x_3540_ = lean_grind_preprocess(v___x_3539_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v_expr_3542_; lean_object* v___x_3543_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v_expr_3542_ = lean_ctor_get(v_a_3541_, 0);
lean_inc_ref(v_expr_3542_);
v___x_3543_ = l_Lean_Meta_Simp_Result_getProof(v_a_3541_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
v___x_3546_ = l_Lean_Expr_constLevels_x21(v___x_3530_);
lean_dec_ref(v___x_3530_);
v___x_3547_ = l_Lean_mkConst(v___x_3545_, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = l_Lean_mkAppRange(v___x_3547_, v___x_3548_, v___x_3510_, v___x_3533_);
lean_inc_ref(v_expr_3542_);
v___x_3550_ = l_Lean_mkApp3(v___x_3549_, v_expr_3542_, v_a_3535_, v_a_3544_);
v___x_3551_ = lean_unbox(v_a_3518_);
lean_dec(v_a_3518_);
v___x_3552_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3497_, v_expr_3542_, v___x_3550_, v___x_3510_, v___x_3533_, v___x_3551_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec_ref(v___x_3533_);
return v___x_3552_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec_ref(v_expr_3542_);
lean_dec(v_a_3535_);
lean_dec_ref(v___x_3533_);
lean_dec_ref(v___x_3530_);
lean_dec(v_a_3518_);
lean_dec_ref(v_e_3497_);
v_a_3553_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3543_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3543_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_a_3535_);
lean_dec_ref(v___x_3533_);
lean_dec_ref(v___x_3530_);
lean_dec(v_a_3518_);
lean_dec_ref(v_e_3497_);
v_a_3561_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3540_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3540_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___x_3533_);
lean_dec_ref(v___x_3530_);
lean_dec(v_a_3518_);
lean_dec_ref(v_c_3516_);
lean_dec_ref(v_e_3497_);
v_a_3569_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3534_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3534_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_a_3518_);
lean_dec_ref(v_c_3516_);
lean_dec(v___x_3514_);
lean_dec(v_numArgs_3509_);
lean_dec_ref(v_e_3497_);
v_a_3578_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3520_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3520_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v_dummy_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec(v_a_3518_);
v___x_3586_ = l_Lean_Expr_getAppFn(v_e_3497_);
v_dummy_3587_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3588_ = lean_mk_array(v_numArgs_3509_, v_dummy_3587_);
lean_inc_ref(v_e_3497_);
v___x_3589_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3497_, v___x_3588_, v___x_3514_);
lean_inc_ref(v_c_3516_);
v___x_3590_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3516_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc_n(v_a_3591_, 2);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = lean_unsigned_to_nat(3u);
v___x_3593_ = lean_array_get_borrowed(v___x_3512_, v___x_3589_, v___x_3592_);
v___x_3594_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3516_, v_a_3591_);
lean_inc(v___x_3593_);
v___x_3595_ = l_Lean_Expr_app___override(v___x_3593_, v___x_3594_);
lean_inc(v_a_3507_);
lean_inc_ref(v_a_3506_);
lean_inc(v_a_3505_);
lean_inc_ref(v_a_3504_);
lean_inc(v_a_3503_);
lean_inc_ref(v_a_3502_);
lean_inc(v_a_3501_);
lean_inc_ref(v_a_3500_);
lean_inc(v_a_3499_);
lean_inc(v_a_3498_);
v___x_3596_ = lean_grind_preprocess(v___x_3595_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v_expr_3598_; lean_object* v___x_3599_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v_expr_3598_ = lean_ctor_get(v_a_3597_, 0);
lean_inc_ref(v_expr_3598_);
v___x_3599_ = l_Lean_Meta_Simp_Result_getProof(v_a_3597_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__3));
v___x_3602_ = l_Lean_Expr_constLevels_x21(v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3603_ = l_Lean_mkConst(v___x_3601_, v___x_3602_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = l_Lean_mkAppRange(v___x_3603_, v___x_3604_, v___x_3510_, v___x_3589_);
lean_inc_ref(v_expr_3598_);
v___x_3606_ = l_Lean_mkApp3(v___x_3605_, v_expr_3598_, v_a_3591_, v_a_3600_);
v___x_3607_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3497_, v_expr_3598_, v___x_3606_, v___x_3510_, v___x_3589_, v___x_3511_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec_ref(v___x_3589_);
return v___x_3607_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v_expr_3598_);
lean_dec(v_a_3591_);
lean_dec_ref(v___x_3589_);
lean_dec_ref(v___x_3586_);
lean_dec_ref(v_e_3497_);
v_a_3608_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3599_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3599_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_a_3591_);
lean_dec_ref(v___x_3589_);
lean_dec_ref(v___x_3586_);
lean_dec_ref(v_e_3497_);
v_a_3616_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3596_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3596_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v___x_3589_);
lean_dec_ref(v___x_3586_);
lean_dec_ref(v_c_3516_);
lean_dec_ref(v_e_3497_);
v_a_3624_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3590_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3590_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v_c_3516_);
lean_dec(v___x_3514_);
lean_dec(v_numArgs_3509_);
lean_dec_ref(v_e_3497_);
v_a_3632_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3517_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3517_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_numArgs_3509_);
lean_dec_ref(v_e_3497_);
v___x_3640_ = lean_box(0);
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
return v___x_3641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object* v_e_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_Meta_Grind_propagateDIte(v_e_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec(v_a_3643_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_));
v___x_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte___boxed), 12, 0);
v___x_3661_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3659_, v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9____boxed(lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_();
return v_res_3663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3682_ = lean_box(0);
v___x_3683_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__8));
v___x_3684_ = l_Lean_mkConst(v___x_3683_, v___x_3682_);
return v___x_3684_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_box(0);
v___x_3691_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__11));
v___x_3692_ = l_Lean_mkConst(v___x_3691_, v___x_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* v_e_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___x_3708_; 
lean_inc_ref(v_e_3693_);
v___x_3708_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_3693_, v_a_3694_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3762_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
uint8_t v_ctor_3713_; 
v_ctor_3713_ = lean_ctor_get_uint8(v_a_3709_, sizeof(void*)*12 + 2);
if (v_ctor_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
lean_dec(v_a_3709_);
lean_dec_ref(v_e_3693_);
v___x_3714_ = lean_box(0);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3714_);
v___x_3716_ = v___x_3711_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
else
{
lean_object* v_self_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_self_3718_ = lean_ctor_get(v_a_3709_, 0);
lean_inc_ref(v_self_3718_);
lean_dec(v_a_3709_);
lean_inc_ref(v_e_3693_);
v___x_3719_ = l_Lean_Expr_cleanupAnnotations(v_e_3693_);
v___x_3720_ = l_Lean_Expr_isApp(v___x_3719_);
if (v___x_3720_ == 0)
{
lean_dec_ref(v___x_3719_);
lean_dec_ref(v_self_3718_);
lean_del_object(v___x_3711_);
lean_dec_ref(v_e_3693_);
goto v___jp_3705_;
}
else
{
lean_object* v_arg_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_arg_3721_ = lean_ctor_get(v___x_3719_, 1);
lean_inc_ref(v_arg_3721_);
v___x_3722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3719_);
v___x_3723_ = l_Lean_Expr_isApp(v___x_3722_);
if (v___x_3723_ == 0)
{
lean_dec_ref(v___x_3722_);
lean_dec_ref(v_arg_3721_);
lean_dec_ref(v_self_3718_);
lean_del_object(v___x_3711_);
lean_dec_ref(v_e_3693_);
goto v___jp_3705_;
}
else
{
lean_object* v_arg_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_arg_3724_ = lean_ctor_get(v___x_3722_, 1);
lean_inc_ref(v_arg_3724_);
v___x_3725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3722_);
v___x_3726_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3727_ = l_Lean_Expr_isConstOf(v___x_3725_, v___x_3726_);
lean_dec_ref(v___x_3725_);
if (v___x_3727_ == 0)
{
lean_dec_ref(v_arg_3724_);
lean_dec_ref(v_arg_3721_);
lean_dec_ref(v_self_3718_);
lean_del_object(v___x_3711_);
lean_dec_ref(v_e_3693_);
goto v___jp_3705_;
}
else
{
lean_object* v___x_3728_; uint8_t v___x_3729_; 
v___x_3728_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
v___x_3729_ = l_Lean_Expr_isConstOf(v_self_3718_, v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3730_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
v___x_3731_ = l_Lean_Expr_isConstOf(v_self_3718_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3734_; 
lean_dec_ref(v_arg_3724_);
lean_dec_ref(v_arg_3721_);
lean_dec_ref(v_self_3718_);
lean_dec_ref(v_e_3693_);
v___x_3732_ = lean_box(0);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3732_);
v___x_3734_ = v___x_3711_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
else
{
lean_object* v___x_3736_; 
lean_del_object(v___x_3711_);
lean_inc(v_a_3703_);
lean_inc_ref(v_a_3702_);
lean_inc(v_a_3701_);
lean_inc_ref(v_a_3700_);
lean_inc(v_a_3699_);
lean_inc_ref(v_a_3698_);
lean_inc(v_a_3697_);
lean_inc_ref(v_a_3696_);
lean_inc(v_a_3695_);
lean_inc(v_a_3694_);
v___x_3736_ = lean_grind_mk_eq_proof(v_e_3693_, v_self_3718_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v___x_3738_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__9, &l_Lean_Meta_Grind_propagateDecideDown___closed__9_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9);
lean_inc_ref(v_arg_3724_);
v___x_3739_ = l_Lean_mkApp3(v___x_3738_, v_arg_3724_, v_arg_3721_, v_a_3737_);
v___x_3740_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_3724_, v___x_3739_, v_a_3694_, v_a_3696_, v_a_3698_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
return v___x_3740_;
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_arg_3724_);
lean_dec_ref(v_arg_3721_);
v_a_3741_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3736_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3736_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_object* v___x_3749_; 
lean_del_object(v___x_3711_);
lean_inc(v_a_3703_);
lean_inc_ref(v_a_3702_);
lean_inc(v_a_3701_);
lean_inc_ref(v_a_3700_);
lean_inc(v_a_3699_);
lean_inc_ref(v_a_3698_);
lean_inc(v_a_3697_);
lean_inc_ref(v_a_3696_);
lean_inc(v_a_3695_);
lean_inc(v_a_3694_);
v___x_3749_ = lean_grind_mk_eq_proof(v_e_3693_, v_self_3718_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
v___x_3751_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__12, &l_Lean_Meta_Grind_propagateDecideDown___closed__12_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12);
lean_inc_ref(v_arg_3724_);
v___x_3752_ = l_Lean_mkApp3(v___x_3751_, v_arg_3724_, v_arg_3721_, v_a_3750_);
v___x_3753_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_3724_, v___x_3752_, v_a_3694_, v_a_3696_, v_a_3698_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
return v___x_3753_;
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v_arg_3724_);
lean_dec_ref(v_arg_3721_);
v_a_3754_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3749_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3749_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
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
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v_e_3693_);
v_a_3763_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3708_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3708_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
v___jp_3705_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_box(0);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object* v_e_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_Grind_propagateDecideDown(v_e_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec(v_a_3772_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3786_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown___boxed), 12, 0);
v___x_3787_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3785_, v___x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9____boxed(lean_object* v_a_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_();
return v_res_3789_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_box(0);
v___x_3796_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__1));
v___x_3797_ = l_Lean_mkConst(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_box(0);
v___x_3804_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__4));
v___x_3805_ = l_Lean_mkConst(v___x_3804_, v___x_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* v_e_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
lean_inc_ref(v_e_3806_);
v___x_3821_ = l_Lean_Expr_cleanupAnnotations(v_e_3806_);
v___x_3822_ = l_Lean_Expr_isApp(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_dec_ref(v___x_3821_);
lean_dec_ref(v_e_3806_);
goto v___jp_3818_;
}
else
{
lean_object* v_arg_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_arg_3823_ = lean_ctor_get(v___x_3821_, 1);
lean_inc_ref(v_arg_3823_);
v___x_3824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3821_);
v___x_3825_ = l_Lean_Expr_isApp(v___x_3824_);
if (v___x_3825_ == 0)
{
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
goto v___jp_3818_;
}
else
{
lean_object* v_arg_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_arg_3826_ = lean_ctor_get(v___x_3824_, 1);
lean_inc_ref(v_arg_3826_);
v___x_3827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3824_);
v___x_3828_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3829_ = l_Lean_Expr_isConstOf(v___x_3827_, v___x_3828_);
lean_dec_ref(v___x_3827_);
if (v___x_3829_ == 0)
{
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
goto v___jp_3818_;
}
else
{
lean_object* v___x_3830_; 
lean_inc_ref(v_arg_3826_);
v___x_3830_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_3826_, v_a_3807_, v_a_3811_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; uint8_t v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = lean_unbox(v_a_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
lean_inc_ref(v_arg_3826_);
v___x_3833_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_3826_, v_a_3807_, v_a_3811_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3867_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3867_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3867_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_unbox(v_a_3834_);
lean_dec(v_a_3834_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3841_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v___x_3839_ = lean_box(0);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3839_);
v___x_3841_ = v___x_3836_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
else
{
lean_object* v___x_3843_; 
lean_del_object(v___x_3836_);
v___x_3843_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3811_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3845_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
lean_inc_ref(v_arg_3826_);
v___x_3845_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_3826_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__2, &l_Lean_Meta_Grind_propagateDecideUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2);
v___x_3848_ = l_Lean_mkApp3(v___x_3847_, v_arg_3826_, v_arg_3823_, v_a_3846_);
v___x_3849_ = lean_unbox(v_a_3831_);
lean_dec(v_a_3831_);
v___x_3850_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3806_, v_a_3844_, v___x_3848_, v___x_3849_, v_a_3807_, v_a_3809_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3850_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_a_3844_);
lean_dec(v_a_3831_);
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3851_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3845_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3845_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3859_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3843_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3843_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_a_3831_);
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3868_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3833_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3833_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec(v_a_3831_);
v___x_3876_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3811_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
lean_inc_ref(v_arg_3826_);
v___x_3878_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_3826_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3880_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__5, &l_Lean_Meta_Grind_propagateDecideUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5);
v___x_3881_ = l_Lean_mkApp3(v___x_3880_, v_arg_3826_, v_arg_3823_, v_a_3879_);
v___x_3882_ = 0;
v___x_3883_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3806_, v_a_3877_, v___x_3881_, v___x_3882_, v_a_3807_, v_a_3809_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3883_;
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3877_);
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3884_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3878_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3878_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3892_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3876_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3876_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v_arg_3826_);
lean_dec_ref(v_arg_3823_);
lean_dec_ref(v_e_3806_);
v_a_3900_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3830_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3830_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
}
v___jp_3818_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_box(0);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
return v___x_3820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object* v_e_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Lean_Meta_Grind_propagateDecideUp(v_e_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec(v_a_3909_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3923_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp___boxed), 12, 0);
v___x_3924_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3922_, v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9____boxed(lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_();
return v_res_3926_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__2));
v___x_3938_ = l_Lean_mkConst(v___x_3937_, v___x_3936_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_box(0);
v___x_3945_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__4));
v___x_3946_ = l_Lean_mkConst(v___x_3945_, v___x_3944_);
return v___x_3946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = lean_box(0);
v___x_3953_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__6));
v___x_3954_ = l_Lean_mkConst(v___x_3953_, v___x_3952_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__8));
v___x_3962_ = l_Lean_mkConst(v___x_3961_, v___x_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* v_e_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
lean_inc_ref(v_e_3963_);
v___x_3978_ = l_Lean_Expr_cleanupAnnotations(v_e_3963_);
v___x_3979_ = l_Lean_Expr_isApp(v___x_3978_);
if (v___x_3979_ == 0)
{
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_e_3963_);
goto v___jp_3975_;
}
else
{
lean_object* v_arg_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v_arg_3980_ = lean_ctor_get(v___x_3978_, 1);
lean_inc_ref(v_arg_3980_);
v___x_3981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3978_);
v___x_3982_ = l_Lean_Expr_isApp(v___x_3981_);
if (v___x_3982_ == 0)
{
lean_dec_ref(v___x_3981_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
goto v___jp_3975_;
}
else
{
lean_object* v_arg_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
v_arg_3983_ = lean_ctor_get(v___x_3981_, 1);
lean_inc_ref(v_arg_3983_);
v___x_3984_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3981_);
v___x_3985_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_3986_ = l_Lean_Expr_isConstOf(v___x_3984_, v___x_3985_);
lean_dec_ref(v___x_3984_);
if (v___x_3986_ == 0)
{
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
goto v___jp_3975_;
}
else
{
lean_object* v___x_3987_; 
lean_inc_ref(v_arg_3983_);
v___x_3987_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3983_, v_a_3964_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = lean_unbox(v_a_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
lean_inc_ref(v_arg_3980_);
v___x_3990_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3980_, v_a_3964_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; uint8_t v___x_3992_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v___x_3992_ = lean_unbox(v_a_3991_);
lean_dec(v_a_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec(v_a_3988_);
lean_inc_ref(v_arg_3983_);
v___x_3993_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3983_, v_a_3964_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; uint8_t v___x_3995_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v___x_3995_ = lean_unbox(v_a_3994_);
lean_dec(v_a_3994_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
lean_inc_ref(v_arg_3980_);
v___x_3996_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3980_, v_a_3964_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4019_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4019_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4019_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
uint8_t v___x_4001_; 
v___x_4001_ = lean_unbox(v_a_3997_);
lean_dec(v_a_3997_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v___x_4002_ = lean_box(0);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4002_);
v___x_4004_ = v___x_3999_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
else
{
lean_object* v___x_4006_; 
lean_del_object(v___x_3999_);
lean_inc_ref(v_arg_3980_);
v___x_4006_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3980_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__3, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3);
v___x_4009_ = l_Lean_mkApp3(v___x_4008_, v_arg_3983_, v_arg_3980_, v_a_4007_);
v___x_4010_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3963_, v___x_4009_, v_a_3964_, v_a_3966_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4010_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4011_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4006_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4006_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4020_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_3996_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_3996_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v___x_4028_; 
lean_inc_ref(v_arg_3983_);
v___x_4028_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3983_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__5, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5);
v___x_4031_ = l_Lean_mkApp3(v___x_4030_, v_arg_3983_, v_arg_3980_, v_a_4029_);
v___x_4032_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3963_, v___x_4031_, v_a_3964_, v_a_3966_, v_a_3968_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4032_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4033_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4028_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4028_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4041_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_3993_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_3993_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v___x_4049_; 
lean_inc_ref(v_arg_3980_);
v___x_4049_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3980_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__7, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7);
lean_inc_ref(v_arg_3983_);
v___x_4052_ = l_Lean_mkApp3(v___x_4051_, v_arg_3983_, v_arg_3980_, v_a_4050_);
v___x_4053_ = lean_unbox(v_a_3988_);
lean_dec(v_a_3988_);
v___x_4054_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3963_, v_arg_3983_, v___x_4052_, v___x_4053_, v_a_3964_, v_a_3966_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4054_;
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v_a_3988_);
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4055_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4049_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4049_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_3988_);
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4063_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_3990_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_3990_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v___x_4071_; 
lean_dec(v_a_3988_);
lean_inc_ref(v_arg_3983_);
v___x_4071_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3983_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; uint8_t v___x_4075_; lean_object* v___x_4076_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__9, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9);
lean_inc_ref(v_arg_3980_);
v___x_4074_ = l_Lean_mkApp3(v___x_4073_, v_arg_3983_, v_arg_3980_, v_a_4072_);
v___x_4075_ = 0;
v___x_4076_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3963_, v_arg_3980_, v___x_4074_, v___x_4075_, v_a_3964_, v_a_3966_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4076_;
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4077_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4071_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4071_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v_arg_3983_);
lean_dec_ref(v_arg_3980_);
lean_dec_ref(v_e_3963_);
v_a_4085_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_3987_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_3987_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
v___jp_3975_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object* v_e_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_Meta_Grind_propagateBoolAndUp(v_e_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec(v_a_4094_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4107_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4108_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp___boxed), 12, 0);
v___x_4109_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4107_, v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9____boxed(lean_object* v_a_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_();
return v_res_4111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = lean_box(0);
v___x_4118_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__0));
v___x_4119_ = l_Lean_mkConst(v___x_4118_, v___x_4117_);
return v___x_4119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_box(0);
v___x_4126_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__2));
v___x_4127_ = l_Lean_mkConst(v___x_4126_, v___x_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* v_e_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___x_4143_; 
lean_inc_ref(v_e_4128_);
v___x_4143_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4128_, v_a_4129_, v_a_4133_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4178_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4178_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4178_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint8_t v___x_4148_; 
v___x_4148_ = lean_unbox(v_a_4144_);
lean_dec(v_a_4144_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; lean_object* v___x_4151_; 
lean_dec_ref(v_e_4128_);
v___x_4149_ = lean_box(0);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4149_);
v___x_4151_ = v___x_4146_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
else
{
lean_object* v___x_4153_; uint8_t v___x_4154_; 
lean_del_object(v___x_4146_);
lean_inc_ref(v_e_4128_);
v___x_4153_ = l_Lean_Expr_cleanupAnnotations(v_e_4128_);
v___x_4154_ = l_Lean_Expr_isApp(v___x_4153_);
if (v___x_4154_ == 0)
{
lean_dec_ref(v___x_4153_);
lean_dec_ref(v_e_4128_);
goto v___jp_4140_;
}
else
{
lean_object* v_arg_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_arg_4155_ = lean_ctor_get(v___x_4153_, 1);
lean_inc_ref(v_arg_4155_);
v___x_4156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4153_);
v___x_4157_ = l_Lean_Expr_isApp(v___x_4156_);
if (v___x_4157_ == 0)
{
lean_dec_ref(v___x_4156_);
lean_dec_ref(v_arg_4155_);
lean_dec_ref(v_e_4128_);
goto v___jp_4140_;
}
else
{
lean_object* v_arg_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_arg_4158_ = lean_ctor_get(v___x_4156_, 1);
lean_inc_ref(v_arg_4158_);
v___x_4159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4156_);
v___x_4160_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4161_ = l_Lean_Expr_isConstOf(v___x_4159_, v___x_4160_);
lean_dec_ref(v___x_4159_);
if (v___x_4161_ == 0)
{
lean_dec_ref(v_arg_4158_);
lean_dec_ref(v_arg_4155_);
lean_dec_ref(v_e_4128_);
goto v___jp_4140_;
}
else
{
lean_object* v___x_4162_; 
v___x_4162_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc_n(v_a_4163_, 2);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__1, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1);
lean_inc_ref(v_arg_4155_);
lean_inc_ref_n(v_arg_4158_, 2);
v___x_4165_ = l_Lean_mkApp3(v___x_4164_, v_arg_4158_, v_arg_4155_, v_a_4163_);
v___x_4166_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4158_, v___x_4165_, v_a_4129_, v_a_4131_, v_a_4133_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec_ref_known(v___x_4166_, 1);
v___x_4167_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__3, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3);
lean_inc_ref(v_arg_4155_);
v___x_4168_ = l_Lean_mkApp3(v___x_4167_, v_arg_4158_, v_arg_4155_, v_a_4163_);
v___x_4169_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4155_, v___x_4168_, v_a_4129_, v_a_4131_, v_a_4133_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4169_;
}
else
{
lean_dec(v_a_4163_);
lean_dec_ref(v_arg_4158_);
lean_dec_ref(v_arg_4155_);
return v___x_4166_;
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_arg_4158_);
lean_dec_ref(v_arg_4155_);
v_a_4170_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4162_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4162_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
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
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec_ref(v_e_4128_);
v_a_4179_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4143_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4143_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
v___jp_4140_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = lean_box(0);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object* v_e_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Meta_Grind_propagateBoolAndDown(v_e_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec(v_a_4188_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4201_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown___boxed), 12, 0);
v___x_4203_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4201_, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9____boxed(lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_();
return v_res_4205_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4215_ = lean_box(0);
v___x_4216_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__2));
v___x_4217_ = l_Lean_mkConst(v___x_4216_, v___x_4215_);
return v___x_4217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_box(0);
v___x_4224_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__4));
v___x_4225_ = l_Lean_mkConst(v___x_4224_, v___x_4223_);
return v___x_4225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4231_ = lean_box(0);
v___x_4232_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__6));
v___x_4233_ = l_Lean_mkConst(v___x_4232_, v___x_4231_);
return v___x_4233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = lean_box(0);
v___x_4240_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__8));
v___x_4241_ = l_Lean_mkConst(v___x_4240_, v___x_4239_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* v_e_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_){
_start:
{
lean_object* v___x_4257_; uint8_t v___x_4258_; 
lean_inc_ref(v_e_4242_);
v___x_4257_ = l_Lean_Expr_cleanupAnnotations(v_e_4242_);
v___x_4258_ = l_Lean_Expr_isApp(v___x_4257_);
if (v___x_4258_ == 0)
{
lean_dec_ref(v___x_4257_);
lean_dec_ref(v_e_4242_);
goto v___jp_4254_;
}
else
{
lean_object* v_arg_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_arg_4259_ = lean_ctor_get(v___x_4257_, 1);
lean_inc_ref(v_arg_4259_);
v___x_4260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4257_);
v___x_4261_ = l_Lean_Expr_isApp(v___x_4260_);
if (v___x_4261_ == 0)
{
lean_dec_ref(v___x_4260_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
goto v___jp_4254_;
}
else
{
lean_object* v_arg_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_arg_4262_ = lean_ctor_get(v___x_4260_, 1);
lean_inc_ref(v_arg_4262_);
v___x_4263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4260_);
v___x_4264_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4265_ = l_Lean_Expr_isConstOf(v___x_4263_, v___x_4264_);
lean_dec_ref(v___x_4263_);
if (v___x_4265_ == 0)
{
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
goto v___jp_4254_;
}
else
{
lean_object* v___x_4266_; 
lean_inc_ref(v_arg_4262_);
v___x_4266_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4262_, v_a_4243_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; uint8_t v___x_4268_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v___x_4268_ = lean_unbox(v_a_4267_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_inc_ref(v_arg_4259_);
v___x_4269_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4259_, v_a_4243_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; uint8_t v___x_4271_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
v___x_4271_ = lean_unbox(v_a_4270_);
lean_dec(v_a_4270_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; 
lean_dec(v_a_4267_);
lean_inc_ref(v_arg_4262_);
v___x_4272_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4262_, v_a_4243_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; uint8_t v___x_4274_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
v___x_4274_ = lean_unbox(v_a_4273_);
lean_dec(v_a_4273_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
lean_inc_ref(v_arg_4259_);
v___x_4275_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4259_, v_a_4243_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4298_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4298_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4298_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_unbox(v_a_4276_);
lean_dec(v_a_4276_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4283_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v___x_4281_ = lean_box(0);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4281_);
v___x_4283_ = v___x_4278_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
else
{
lean_object* v___x_4285_; 
lean_del_object(v___x_4278_);
lean_inc_ref(v_arg_4259_);
v___x_4285_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4259_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__3, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3);
v___x_4288_ = l_Lean_mkApp3(v___x_4287_, v_arg_4262_, v_arg_4259_, v_a_4286_);
v___x_4289_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4242_, v___x_4288_, v_a_4243_, v_a_4245_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4289_;
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4290_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4285_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4285_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4299_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4275_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4275_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_object* v___x_4307_; 
lean_inc_ref(v_arg_4262_);
v___x_4307_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4262_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__5, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5);
v___x_4310_ = l_Lean_mkApp3(v___x_4309_, v_arg_4262_, v_arg_4259_, v_a_4308_);
v___x_4311_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4242_, v___x_4310_, v_a_4243_, v_a_4245_, v_a_4247_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4311_;
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4312_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4307_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4307_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4320_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4272_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4272_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_object* v___x_4328_; 
lean_inc_ref(v_arg_4259_);
v___x_4328_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4259_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; lean_object* v___x_4333_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4330_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__7, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7);
lean_inc_ref(v_arg_4262_);
v___x_4331_ = l_Lean_mkApp3(v___x_4330_, v_arg_4262_, v_arg_4259_, v_a_4329_);
v___x_4332_ = lean_unbox(v_a_4267_);
lean_dec(v_a_4267_);
v___x_4333_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4242_, v_arg_4262_, v___x_4331_, v___x_4332_, v_a_4243_, v_a_4245_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4333_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4267_);
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4334_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4328_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4328_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_dec(v_a_4267_);
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4342_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4269_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4269_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
else
{
lean_object* v___x_4350_; 
lean_dec(v_a_4267_);
lean_inc_ref(v_arg_4262_);
v___x_4350_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4262_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; lean_object* v___x_4355_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__9, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9);
lean_inc_ref(v_arg_4259_);
v___x_4353_ = l_Lean_mkApp3(v___x_4352_, v_arg_4262_, v_arg_4259_, v_a_4351_);
v___x_4354_ = 0;
v___x_4355_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4242_, v_arg_4259_, v___x_4353_, v___x_4354_, v_a_4243_, v_a_4245_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4355_;
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4356_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4350_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4350_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref(v_arg_4262_);
lean_dec_ref(v_arg_4259_);
lean_dec_ref(v_e_4242_);
v_a_4364_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4266_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4266_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
}
v___jp_4254_:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = lean_box(0);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object* v_e_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_Meta_Grind_propagateBoolOrUp(v_e_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
lean_dec(v_a_4382_);
lean_dec_ref(v_a_4381_);
lean_dec(v_a_4380_);
lean_dec_ref(v_a_4379_);
lean_dec(v_a_4378_);
lean_dec_ref(v_a_4377_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec(v_a_4373_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4386_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4387_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp___boxed), 12, 0);
v___x_4388_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4386_, v___x_4387_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9____boxed(lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_();
return v_res_4390_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4396_ = lean_box(0);
v___x_4397_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__0));
v___x_4398_ = l_Lean_mkConst(v___x_4397_, v___x_4396_);
return v___x_4398_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__2));
v___x_4406_ = l_Lean_mkConst(v___x_4405_, v___x_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* v_e_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v___x_4422_; 
lean_inc_ref(v_e_4407_);
v___x_4422_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4407_, v_a_4408_, v_a_4412_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4457_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4457_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4457_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
uint8_t v___x_4427_; 
v___x_4427_ = lean_unbox(v_a_4423_);
lean_dec(v_a_4423_);
if (v___x_4427_ == 0)
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
lean_dec_ref(v_e_4407_);
v___x_4428_ = lean_box(0);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4428_);
v___x_4430_ = v___x_4425_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
else
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
lean_del_object(v___x_4425_);
lean_inc_ref(v_e_4407_);
v___x_4432_ = l_Lean_Expr_cleanupAnnotations(v_e_4407_);
v___x_4433_ = l_Lean_Expr_isApp(v___x_4432_);
if (v___x_4433_ == 0)
{
lean_dec_ref(v___x_4432_);
lean_dec_ref(v_e_4407_);
goto v___jp_4419_;
}
else
{
lean_object* v_arg_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v_arg_4434_ = lean_ctor_get(v___x_4432_, 1);
lean_inc_ref(v_arg_4434_);
v___x_4435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4432_);
v___x_4436_ = l_Lean_Expr_isApp(v___x_4435_);
if (v___x_4436_ == 0)
{
lean_dec_ref(v___x_4435_);
lean_dec_ref(v_arg_4434_);
lean_dec_ref(v_e_4407_);
goto v___jp_4419_;
}
else
{
lean_object* v_arg_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; uint8_t v___x_4440_; 
v_arg_4437_ = lean_ctor_get(v___x_4435_, 1);
lean_inc_ref(v_arg_4437_);
v___x_4438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4435_);
v___x_4439_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4440_ = l_Lean_Expr_isConstOf(v___x_4438_, v___x_4439_);
lean_dec_ref(v___x_4438_);
if (v___x_4440_ == 0)
{
lean_dec_ref(v_arg_4437_);
lean_dec_ref(v_arg_4434_);
lean_dec_ref(v_e_4407_);
goto v___jp_4419_;
}
else
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc_n(v_a_4442_, 2);
lean_dec_ref_known(v___x_4441_, 1);
v___x_4443_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__1, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1);
lean_inc_ref(v_arg_4434_);
lean_inc_ref_n(v_arg_4437_, 2);
v___x_4444_ = l_Lean_mkApp3(v___x_4443_, v_arg_4437_, v_arg_4434_, v_a_4442_);
v___x_4445_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4437_, v___x_4444_, v_a_4408_, v_a_4410_, v_a_4412_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
lean_dec_ref_known(v___x_4445_, 1);
v___x_4446_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__3, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3);
lean_inc_ref(v_arg_4434_);
v___x_4447_ = l_Lean_mkApp3(v___x_4446_, v_arg_4437_, v_arg_4434_, v_a_4442_);
v___x_4448_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4434_, v___x_4447_, v_a_4408_, v_a_4410_, v_a_4412_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4448_;
}
else
{
lean_dec(v_a_4442_);
lean_dec_ref(v_arg_4437_);
lean_dec_ref(v_arg_4434_);
return v___x_4445_;
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec_ref(v_arg_4437_);
lean_dec_ref(v_arg_4434_);
v_a_4449_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4441_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4441_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
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
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref(v_e_4407_);
v_a_4458_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4422_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4422_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
v___jp_4419_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = lean_box(0);
v___x_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
return v___x_4421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object* v_e_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Meta_Grind_propagateBoolOrDown(v_e_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec(v_a_4467_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4480_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4481_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown___boxed), 12, 0);
v___x_4482_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4480_, v___x_4481_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9____boxed(lean_object* v_a_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_();
return v_res_4484_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_box(0);
v___x_4495_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__2));
v___x_4496_ = l_Lean_mkConst(v___x_4495_, v___x_4494_);
return v___x_4496_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = lean_box(0);
v___x_4503_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__4));
v___x_4504_ = l_Lean_mkConst(v___x_4503_, v___x_4502_);
return v___x_4504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7(void){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_box(0);
v___x_4511_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__6));
v___x_4512_ = l_Lean_mkConst(v___x_4511_, v___x_4510_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* v_e_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
lean_inc_ref(v_e_4513_);
v___x_4528_ = l_Lean_Expr_cleanupAnnotations(v_e_4513_);
v___x_4529_ = l_Lean_Expr_isApp(v___x_4528_);
if (v___x_4529_ == 0)
{
lean_dec_ref(v___x_4528_);
lean_dec_ref(v_e_4513_);
goto v___jp_4525_;
}
else
{
lean_object* v_arg_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v_arg_4530_ = lean_ctor_get(v___x_4528_, 1);
lean_inc_ref(v_arg_4530_);
v___x_4531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4528_);
v___x_4532_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4533_ = l_Lean_Expr_isConstOf(v___x_4531_, v___x_4532_);
lean_dec_ref(v___x_4531_);
if (v___x_4533_ == 0)
{
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
goto v___jp_4525_;
}
else
{
lean_object* v___x_4534_; 
lean_inc_ref(v_arg_4530_);
v___x_4534_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4530_, v_a_4514_, v_a_4518_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; uint8_t v___x_4536_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___x_4536_ = lean_unbox(v_a_4535_);
lean_dec(v_a_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_inc_ref(v_arg_4530_);
v___x_4537_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4530_, v_a_4514_, v_a_4518_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; uint8_t v___x_4539_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v___x_4539_ = lean_unbox(v_a_4538_);
lean_dec(v_a_4538_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4513_, v_arg_4530_, v_a_4514_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4563_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4563_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4563_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
uint8_t v___x_4545_; 
v___x_4545_ = lean_unbox(v_a_4541_);
lean_dec(v_a_4541_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v___x_4548_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v___x_4546_ = lean_box(0);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4546_);
v___x_4548_ = v___x_4543_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_object* v___x_4550_; 
lean_del_object(v___x_4543_);
lean_inc(v_a_4523_);
lean_inc_ref(v_a_4522_);
lean_inc(v_a_4521_);
lean_inc_ref(v_a_4520_);
lean_inc(v_a_4519_);
lean_inc_ref(v_a_4518_);
lean_inc(v_a_4517_);
lean_inc_ref(v_a_4516_);
lean_inc(v_a_4515_);
lean_inc(v_a_4514_);
lean_inc_ref(v_arg_4530_);
v___x_4550_ = lean_grind_mk_eq_proof(v_e_4513_, v_arg_4530_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v___x_4552_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4553_ = l_Lean_mkAppB(v___x_4552_, v_arg_4530_, v_a_4551_);
v___x_4554_ = l_Lean_Meta_Grind_closeGoal(v___x_4553_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v_arg_4530_);
v_a_4555_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4550_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4550_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v_a_4564_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4540_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4540_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v___x_4572_; 
lean_inc_ref(v_arg_4530_);
v___x_4572_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4530_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v___x_4574_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__5, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5);
v___x_4575_ = l_Lean_mkAppB(v___x_4574_, v_arg_4530_, v_a_4573_);
v___x_4576_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4513_, v___x_4575_, v_a_4514_, v_a_4516_, v_a_4518_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
return v___x_4576_;
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v_a_4577_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4572_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4572_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v_a_4585_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4537_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4537_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
else
{
lean_object* v___x_4593_; 
lean_inc_ref(v_arg_4530_);
v___x_4593_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4530_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4593_, 1);
v___x_4595_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__7, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7);
v___x_4596_ = l_Lean_mkAppB(v___x_4595_, v_arg_4530_, v_a_4594_);
v___x_4597_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4513_, v___x_4596_, v_a_4514_, v_a_4516_, v_a_4518_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
return v___x_4597_;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v_a_4598_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4593_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4593_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v_arg_4530_);
lean_dec_ref(v_e_4513_);
v_a_4606_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4534_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4534_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
}
v___jp_4525_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = lean_box(0);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object* v_e_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_Meta_Grind_propagateBoolNotUp(v_e_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec(v_a_4615_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4629_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp___boxed), 12, 0);
v___x_4630_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4628_, v___x_4629_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9____boxed(lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_();
return v_res_4632_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = lean_box(0);
v___x_4639_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__0));
v___x_4640_ = l_Lean_mkConst(v___x_4639_, v___x_4638_);
return v___x_4640_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = lean_box(0);
v___x_4647_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__2));
v___x_4648_ = l_Lean_mkConst(v___x_4647_, v___x_4646_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* v_e_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_){
_start:
{
lean_object* v___x_4664_; uint8_t v___x_4665_; 
lean_inc_ref(v_e_4649_);
v___x_4664_ = l_Lean_Expr_cleanupAnnotations(v_e_4649_);
v___x_4665_ = l_Lean_Expr_isApp(v___x_4664_);
if (v___x_4665_ == 0)
{
lean_dec_ref(v___x_4664_);
lean_dec_ref(v_e_4649_);
goto v___jp_4661_;
}
else
{
lean_object* v_arg_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v_arg_4666_ = lean_ctor_get(v___x_4664_, 1);
lean_inc_ref(v_arg_4666_);
v___x_4667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4664_);
v___x_4668_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4669_ = l_Lean_Expr_isConstOf(v___x_4667_, v___x_4668_);
lean_dec_ref(v___x_4667_);
if (v___x_4669_ == 0)
{
lean_dec_ref(v_arg_4666_);
lean_dec_ref(v_e_4649_);
goto v___jp_4661_;
}
else
{
lean_object* v___x_4670_; 
lean_inc_ref(v_e_4649_);
v___x_4670_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4649_, v_a_4650_, v_a_4654_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; uint8_t v___x_4672_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = lean_unbox(v_a_4671_);
lean_dec(v_a_4671_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
lean_inc_ref(v_e_4649_);
v___x_4673_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4649_, v_a_4650_, v_a_4654_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; uint8_t v___x_4675_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v___x_4675_ = lean_unbox(v_a_4674_);
lean_dec(v_a_4674_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4649_, v_arg_4666_, v_a_4650_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4699_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4699_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4699_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
uint8_t v___x_4681_; 
v___x_4681_ = lean_unbox(v_a_4677_);
lean_dec(v_a_4677_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; lean_object* v___x_4684_; 
lean_dec_ref(v_arg_4666_);
lean_dec_ref(v_e_4649_);
v___x_4682_ = lean_box(0);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 0, v___x_4682_);
v___x_4684_ = v___x_4679_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
else
{
lean_object* v___x_4686_; 
lean_del_object(v___x_4679_);
lean_inc(v_a_4659_);
lean_inc_ref(v_a_4658_);
lean_inc(v_a_4657_);
lean_inc_ref(v_a_4656_);
lean_inc(v_a_4655_);
lean_inc_ref(v_a_4654_);
lean_inc(v_a_4653_);
lean_inc_ref(v_a_4652_);
lean_inc(v_a_4651_);
lean_inc(v_a_4650_);
lean_inc_ref(v_arg_4666_);
v___x_4686_ = lean_grind_mk_eq_proof(v_e_4649_, v_arg_4666_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4688_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4689_ = l_Lean_mkAppB(v___x_4688_, v_arg_4666_, v_a_4687_);
v___x_4690_ = l_Lean_Meta_Grind_closeGoal(v___x_4689_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
return v___x_4690_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec_ref(v_arg_4666_);
v_a_4691_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4686_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4686_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec_ref(v_arg_4666_);
lean_dec_ref(v_e_4649_);
v_a_4700_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4676_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4676_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
else
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v___x_4708_, 1);
v___x_4710_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__1, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1);
lean_inc_ref(v_arg_4666_);
v___x_4711_ = l_Lean_mkAppB(v___x_4710_, v_arg_4666_, v_a_4709_);
v___x_4712_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4666_, v___x_4711_, v_a_4650_, v_a_4652_, v_a_4654_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
return v___x_4712_;
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v_arg_4666_);
v_a_4713_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4708_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4708_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref(v_arg_4666_);
lean_dec_ref(v_e_4649_);
v_a_4721_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4673_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4673_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
else
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
v___x_4731_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__3, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3);
lean_inc_ref(v_arg_4666_);
v___x_4732_ = l_Lean_mkAppB(v___x_4731_, v_arg_4666_, v_a_4730_);
v___x_4733_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4666_, v___x_4732_, v_a_4650_, v_a_4652_, v_a_4654_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_);
return v___x_4733_;
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec_ref(v_arg_4666_);
v_a_4734_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4729_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4729_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec_ref(v_arg_4666_);
lean_dec_ref(v_e_4649_);
v_a_4742_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4670_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4670_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
v___jp_4661_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = lean_box(0);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object* v_e_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Meta_Grind_propagateBoolNotDown(v_e_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec(v_a_4751_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4765_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown___boxed), 12, 0);
v___x_4766_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4764_, v___x_4765_);
return v___x_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9____boxed(lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_();
return v_res_4768_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
}
#ifdef __cplusplus
}
#endif
