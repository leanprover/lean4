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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProofUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_false_of_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ne_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBoolDiseq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "eq_eq_of_eq_true_right"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(109, 195, 236, 103, 135, 232, 42, 67)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateEqUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateEqUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "eq_eq_of_eq_true_left"};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 111, 216, 64, 67, 213, 235, 199)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqUp___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateEqUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateEqUp___closed__10;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateAndUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateEqMatchDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateHEqDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateHEqDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_Grind_propagateHEqDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateHEqDown___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Grind_propagateIte___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateIte___closed__0;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l_Lean_Meta_Grind_propagateIte___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateIte___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndUp___boxed), 12, 0);
v___x_184_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8____boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_277_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndDown___boxed), 12, 0);
v___x_278_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8____boxed(lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_461_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrUp___boxed), 12, 0);
v___x_462_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_460_, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8____boxed(lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_555_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrDown___boxed), 12, 0);
v___x_556_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8____boxed(lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_702_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotUp___boxed), 12, 0);
v___x_703_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_701_, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8____boxed(lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_838_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotDown___boxed), 12, 0);
v___x_839_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_837_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8____boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object* v_arg_1014_, lean_object* v_self_1015_, lean_object* v_arg_1016_, lean_object* v_self_1017_, uint8_t v_a_1018_, uint8_t v___x_1019_, lean_object* v_hab_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_hf_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___x_1048_; 
lean_inc_ref(v_self_1015_);
lean_inc_ref(v_arg_1014_);
v___x_1048_ = l_Lean_Meta_Grind_hasSameType(v_arg_1014_, v_self_1015_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
lean_inc_ref(v_self_1017_);
lean_inc_ref(v_arg_1016_);
v___x_1050_ = l_Lean_Meta_Grind_hasSameType(v_arg_1016_, v_self_1017_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___x_1075_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1075_ = lean_unbox(v_a_1049_);
lean_dec(v_a_1049_);
if (v___x_1075_ == 1)
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
if (v___x_1076_ == 1)
{
lean_object* v___x_1077_; 
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
v___x_1077_ = lean_grind_mk_eq_proof(v_self_1015_, v_arg_1014_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
lean_inc_ref(v_hab_1020_);
v___x_1079_ = l_Lean_Meta_mkEqTrans(v_a_1078_, v_hab_1020_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
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
v___x_1081_ = lean_grind_mk_eq_proof(v_arg_1016_, v_self_1017_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Lean_Meta_mkEqTrans(v_a_1080_, v_a_1082_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_hf_1033_ = v_a_1084_;
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
return v___x_1083_;
}
}
else
{
lean_dec(v_a_1080_);
lean_dec_ref(v_hab_1020_);
return v___x_1081_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
return v___x_1079_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
return v___x_1077_;
}
}
else
{
v___y_1053_ = v___y_1021_;
v___y_1054_ = v___y_1022_;
v___y_1055_ = v___y_1023_;
v___y_1056_ = v___y_1024_;
v___y_1057_ = v___y_1025_;
v___y_1058_ = v___y_1026_;
v___y_1059_ = v___y_1027_;
v___y_1060_ = v___y_1028_;
v___y_1061_ = v___y_1029_;
v___y_1062_ = v___y_1030_;
goto v___jp_1052_;
}
}
else
{
lean_dec(v_a_1051_);
v___y_1053_ = v___y_1021_;
v___y_1054_ = v___y_1022_;
v___y_1055_ = v___y_1023_;
v___y_1056_ = v___y_1024_;
v___y_1057_ = v___y_1025_;
v___y_1058_ = v___y_1026_;
v___y_1059_ = v___y_1027_;
v___y_1060_ = v___y_1028_;
v___y_1061_ = v___y_1029_;
v___y_1062_ = v___y_1030_;
goto v___jp_1052_;
}
v___jp_1052_:
{
lean_object* v___x_1063_; 
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc(v___y_1053_);
v___x_1063_ = lean_grind_mk_heq_proof(v_self_1015_, v_arg_1014_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
lean_inc_ref(v_hab_1020_);
v___x_1065_ = l_Lean_Meta_mkHEqOfEq(v_hab_1020_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = l_Lean_Meta_mkHEqTrans(v_a_1064_, v_a_1066_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc(v___y_1053_);
v___x_1069_ = lean_grind_mk_heq_proof(v_arg_1016_, v_self_1017_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = l_Lean_Meta_mkHEqTrans(v_a_1068_, v_a_1070_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = l_Lean_Meta_mkEqOfHEq(v_a_1072_, v___x_1019_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_hf_1033_ = v_a_1074_;
v___y_1034_ = v___y_1057_;
v___y_1035_ = v___y_1059_;
v___y_1036_ = v___y_1060_;
v___y_1037_ = v___y_1061_;
v___y_1038_ = v___y_1062_;
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
lean_dec_ref(v_hab_1020_);
return v___x_1071_;
}
}
else
{
lean_dec(v_a_1068_);
lean_dec_ref(v_hab_1020_);
return v___x_1069_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
return v___x_1067_;
}
}
else
{
lean_dec(v_a_1064_);
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
return v___x_1065_;
}
}
else
{
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
return v___x_1063_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_a_1049_);
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
lean_dec_ref(v_self_1015_);
lean_dec_ref(v_arg_1014_);
v_a_1085_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1050_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1050_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v_hab_1020_);
lean_dec_ref(v_self_1017_);
lean_dec_ref(v_arg_1016_);
lean_dec_ref(v_self_1015_);
lean_dec_ref(v_arg_1014_);
v_a_1093_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1048_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1048_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
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
v___x_1047_ = l_Lean_Meta_mkLambdaFVars(v___x_1045_, v_a_1042_, v_a_1018_, v___x_1019_, v_a_1018_, v___x_1019_, v___x_1046_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object** _args){
lean_object* v_arg_1101_ = _args[0];
lean_object* v_self_1102_ = _args[1];
lean_object* v_arg_1103_ = _args[2];
lean_object* v_self_1104_ = _args[3];
lean_object* v_a_1105_ = _args[4];
lean_object* v___x_1106_ = _args[5];
lean_object* v_hab_1107_ = _args[6];
lean_object* v___y_1108_ = _args[7];
lean_object* v___y_1109_ = _args[8];
lean_object* v___y_1110_ = _args[9];
lean_object* v___y_1111_ = _args[10];
lean_object* v___y_1112_ = _args[11];
lean_object* v___y_1113_ = _args[12];
lean_object* v___y_1114_ = _args[13];
lean_object* v___y_1115_ = _args[14];
lean_object* v___y_1116_ = _args[15];
lean_object* v___y_1117_ = _args[16];
lean_object* v___y_1118_ = _args[17];
_start:
{
uint8_t v_a_138002__boxed_1119_; uint8_t v___x_138003__boxed_1120_; lean_object* v_res_1121_; 
v_a_138002__boxed_1119_ = lean_unbox(v_a_1105_);
v___x_138003__boxed_1120_ = lean_unbox(v___x_1106_);
v_res_1121_ = l_Lean_Meta_Grind_propagateEqUp___lam__0(v_arg_1101_, v_self_1102_, v_arg_1103_, v_self_1104_, v_a_138002__boxed_1119_, v___x_138003__boxed_1120_, v_hab_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc(v___y_1123_);
v___x_1135_ = lean_apply_12(v_k_1122_, v_b_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, lean_box(0));
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(v_k_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec(v___y_1137_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object* v_name_1150_, uint8_t v_bi_1151_, lean_object* v_type_1152_, lean_object* v_k_1153_, uint8_t v_kind_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___f_1166_; lean_object* v___x_1167_; 
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc(v___y_1155_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1166_, 0, v_k_1153_);
lean_closure_set(v___f_1166_, 1, v___y_1155_);
lean_closure_set(v___f_1166_, 2, v___y_1156_);
lean_closure_set(v___f_1166_, 3, v___y_1157_);
lean_closure_set(v___f_1166_, 4, v___y_1158_);
lean_closure_set(v___f_1166_, 5, v___y_1159_);
lean_closure_set(v___f_1166_, 6, v___y_1160_);
v___x_1167_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1150_, v_bi_1151_, v_type_1152_, v___f_1166_, v_kind_1154_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
return v___x_1167_;
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object* v_name_1176_, lean_object* v_bi_1177_, lean_object* v_type_1178_, lean_object* v_k_1179_, lean_object* v_kind_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_bi_boxed_1192_; uint8_t v_kind_boxed_1193_; lean_object* v_res_1194_; 
v_bi_boxed_1192_ = lean_unbox(v_bi_1177_);
v_kind_boxed_1193_ = lean_unbox(v_kind_1180_);
v_res_1194_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1176_, v_bi_boxed_1192_, v_type_1178_, v_k_1179_, v_kind_boxed_1193_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object* v_name_1195_, lean_object* v_type_1196_, lean_object* v_k_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = 0;
v___x_1210_ = 0;
v___x_1211_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1195_, v___x_1209_, v_type_1196_, v_k_1197_, v___x_1210_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object* v_name_1212_, lean_object* v_type_1213_, lean_object* v_k_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_1212_, v_type_1213_, v_k_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec(v___y_1215_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(lean_object* v_a_1227_, lean_object* v_self_1228_, lean_object* v_a_1229_, lean_object* v_self_1230_, uint8_t v_a_1231_, uint8_t v___x_1232_, lean_object* v_hab_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_hf_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___x_1261_; 
lean_inc_ref(v_self_1228_);
lean_inc_ref(v_a_1227_);
v___x_1261_ = l_Lean_Meta_Grind_hasSameType(v_a_1227_, v_self_1228_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
lean_inc_ref(v_self_1230_);
lean_inc_ref(v_a_1229_);
v___x_1263_ = l_Lean_Meta_Grind_hasSameType(v_a_1229_, v_self_1230_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v___x_1288_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1288_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1288_ == 1)
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_unbox(v_a_1264_);
lean_dec(v_a_1264_);
if (v___x_1289_ == 1)
{
lean_object* v___x_1290_; 
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc(v___y_1234_);
v___x_1290_ = lean_grind_mk_eq_proof(v_self_1228_, v_a_1227_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
lean_inc_ref(v_hab_1233_);
v___x_1292_ = l_Lean_Meta_mkEqTrans(v_a_1291_, v_hab_1233_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc(v___y_1234_);
v___x_1294_ = lean_grind_mk_eq_proof(v_a_1229_, v_self_1230_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = l_Lean_Meta_mkEqTrans(v_a_1293_, v_a_1295_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v_hf_1246_ = v_a_1297_;
v___y_1247_ = v___y_1238_;
v___y_1248_ = v___y_1240_;
v___y_1249_ = v___y_1241_;
v___y_1250_ = v___y_1242_;
v___y_1251_ = v___y_1243_;
goto v___jp_1245_;
}
else
{
lean_dec_ref(v_hab_1233_);
return v___x_1296_;
}
}
else
{
lean_dec(v_a_1293_);
lean_dec_ref(v_hab_1233_);
return v___x_1294_;
}
}
else
{
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1292_;
}
}
else
{
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1290_;
}
}
else
{
v___y_1266_ = v___y_1234_;
v___y_1267_ = v___y_1235_;
v___y_1268_ = v___y_1236_;
v___y_1269_ = v___y_1237_;
v___y_1270_ = v___y_1238_;
v___y_1271_ = v___y_1239_;
v___y_1272_ = v___y_1240_;
v___y_1273_ = v___y_1241_;
v___y_1274_ = v___y_1242_;
v___y_1275_ = v___y_1243_;
goto v___jp_1265_;
}
}
else
{
lean_dec(v_a_1264_);
v___y_1266_ = v___y_1234_;
v___y_1267_ = v___y_1235_;
v___y_1268_ = v___y_1236_;
v___y_1269_ = v___y_1237_;
v___y_1270_ = v___y_1238_;
v___y_1271_ = v___y_1239_;
v___y_1272_ = v___y_1240_;
v___y_1273_ = v___y_1241_;
v___y_1274_ = v___y_1242_;
v___y_1275_ = v___y_1243_;
goto v___jp_1265_;
}
v___jp_1265_:
{
lean_object* v___x_1276_; 
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1276_ = lean_grind_mk_heq_proof(v_self_1228_, v_a_1227_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
lean_inc_ref(v_hab_1233_);
v___x_1278_ = l_Lean_Meta_mkHEqOfEq(v_hab_1233_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = l_Lean_Meta_mkHEqTrans(v_a_1277_, v_a_1279_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1282_ = lean_grind_mk_heq_proof(v_a_1229_, v_self_1230_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = l_Lean_Meta_mkHEqTrans(v_a_1281_, v_a_1283_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_Meta_mkEqOfHEq(v_a_1285_, v___x_1232_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v_hf_1246_ = v_a_1287_;
v___y_1247_ = v___y_1270_;
v___y_1248_ = v___y_1272_;
v___y_1249_ = v___y_1273_;
v___y_1250_ = v___y_1274_;
v___y_1251_ = v___y_1275_;
goto v___jp_1245_;
}
else
{
lean_dec_ref(v_hab_1233_);
return v___x_1286_;
}
}
else
{
lean_dec_ref(v_hab_1233_);
return v___x_1284_;
}
}
else
{
lean_dec(v_a_1281_);
lean_dec_ref(v_hab_1233_);
return v___x_1282_;
}
}
else
{
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1280_;
}
}
else
{
lean_dec(v_a_1277_);
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1278_;
}
}
else
{
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1262_);
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
lean_dec_ref(v_self_1228_);
lean_dec_ref(v_a_1227_);
v_a_1298_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1263_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1263_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_hab_1233_);
lean_dec_ref(v_self_1230_);
lean_dec_ref(v_a_1229_);
lean_dec_ref(v_self_1228_);
lean_dec_ref(v_a_1227_);
v_a_1306_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1261_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1261_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
v___jp_1245_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1247_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = l_Lean_Meta_mkNoConfusion(v_a_1253_, v_hf_1246_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_mk_empty_array_with_capacity(v___x_1256_);
v___x_1258_ = lean_array_push(v___x_1257_, v_hab_1233_);
v___x_1259_ = 1;
v___x_1260_ = l_Lean_Meta_mkLambdaFVars(v___x_1258_, v_a_1255_, v_a_1231_, v___x_1232_, v_a_1231_, v___x_1232_, v___x_1259_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec_ref(v___x_1258_);
return v___x_1260_;
}
else
{
lean_dec_ref(v_hab_1233_);
return v___x_1254_;
}
}
else
{
lean_dec_ref(v_hf_1246_);
lean_dec_ref(v_hab_1233_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1314_ = _args[0];
lean_object* v_self_1315_ = _args[1];
lean_object* v_a_1316_ = _args[2];
lean_object* v_self_1317_ = _args[3];
lean_object* v_a_1318_ = _args[4];
lean_object* v___x_1319_ = _args[5];
lean_object* v_hab_1320_ = _args[6];
lean_object* v___y_1321_ = _args[7];
lean_object* v___y_1322_ = _args[8];
lean_object* v___y_1323_ = _args[9];
lean_object* v___y_1324_ = _args[10];
lean_object* v___y_1325_ = _args[11];
lean_object* v___y_1326_ = _args[12];
lean_object* v___y_1327_ = _args[13];
lean_object* v___y_1328_ = _args[14];
lean_object* v___y_1329_ = _args[15];
lean_object* v___y_1330_ = _args[16];
lean_object* v___y_1331_ = _args[17];
_start:
{
uint8_t v_a_138323__boxed_1332_; uint8_t v___x_138324__boxed_1333_; lean_object* v_res_1334_; 
v_a_138323__boxed_1332_ = lean_unbox(v_a_1318_);
v___x_138324__boxed_1333_ = lean_unbox(v___x_1319_);
v_res_1334_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(v_a_1314_, v_self_1315_, v_a_1316_, v_self_1317_, v_a_138323__boxed_1332_, v___x_138324__boxed_1333_, v_hab_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
return v_res_1334_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1));
v___x_1340_ = l_Lean_mkConst(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_e_1346_, uint8_t v___x_1347_, uint8_t v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1448_; 
v___x_1362_ = lean_st_ref_get(v___y_1351_);
v_snd_1363_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_a_1350_, 0);
lean_dec(v_unused_1449_);
v___x_1365_ = v_a_1350_;
v_isShared_1366_ = v_isSharedCheck_1448_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_a_1350_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1448_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v_a_1368_; lean_object* v___y_1376_; lean_object* v___x_1397_; 
lean_inc(v_snd_1363_);
v___x_1397_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1362_, v_snd_1363_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___x_1362_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1439_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1439_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1439_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_self_1402_; lean_object* v_next_1403_; uint8_t v_ctor_1404_; lean_object* v___x_1405_; 
v_self_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc_ref(v_self_1402_);
v_next_1403_ = lean_ctor_get(v_a_1398_, 1);
lean_inc_ref(v_next_1403_);
v_ctor_1404_ = lean_ctor_get_uint8(v_a_1398_, sizeof(void*)*12 + 2);
lean_dec(v_a_1398_);
v___x_1405_ = lean_box(0);
if (v_ctor_1404_ == 0)
{
lean_dec_ref(v_self_1402_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
else
{
lean_object* v_self_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v_self_1414_ = lean_ctor_get(v_a_1345_, 0);
v___x_1415_ = l_Lean_Expr_getAppFn(v_self_1414_);
v___x_1416_ = l_Lean_Expr_getAppFn(v_self_1402_);
v___x_1417_ = lean_expr_eqv(v___x_1415_, v___x_1416_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_inc_ref(v_self_1402_);
lean_inc_ref(v_self_1414_);
v___x_1418_ = l_Lean_Meta_Grind_hasSameType(v_self_1414_, v_self_1402_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; uint8_t v___x_1420_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_unbox(v_a_1419_);
lean_dec(v_a_1419_);
if (v___x_1420_ == 0)
{
lean_dec_ref(v_self_1402_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
else
{
lean_object* v___x_1421_; 
lean_inc_ref(v_self_1414_);
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_dec_ref(v_a_1345_);
lean_inc_ref(v_a_1344_);
lean_inc_ref(v_a_1349_);
v___x_1421_ = l_Lean_Meta_mkEq(v_a_1349_, v_a_1344_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = lean_box(v_a_1348_);
v___x_1424_ = lean_box(v___x_1347_);
v___f_1425_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1425_, 0, v_a_1349_);
lean_closure_set(v___f_1425_, 1, v_self_1414_);
lean_closure_set(v___f_1425_, 2, v_a_1344_);
lean_closure_set(v___f_1425_, 3, v_self_1402_);
lean_closure_set(v___f_1425_, 4, v___x_1423_);
lean_closure_set(v___f_1425_, 5, v___x_1424_);
v___x_1426_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1427_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1426_, v_a_1422_, v___f_1425_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1376_ = v___x_1427_;
goto v___jp_1375_;
}
else
{
lean_dec_ref(v_self_1414_);
lean_dec_ref(v_self_1402_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_a_1344_);
v___y_1376_ = v___x_1421_;
goto v___jp_1375_;
}
}
}
else
{
lean_dec_ref(v_self_1402_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1428_; uint8_t v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1429_ = lean_unbox(v_a_1428_);
if (v___x_1429_ == 0)
{
lean_dec(v_a_1428_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
else
{
uint8_t v___x_1430_; 
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v___x_1430_ = lean_unbox(v_a_1428_);
lean_dec(v_a_1428_);
v_a_1368_ = v___x_1430_;
goto v___jp_1367_;
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v_a_1431_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1418_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1418_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_1402_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
}
v___jp_1406_:
{
uint8_t v___x_1407_; 
v___x_1407_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_1403_, v_a_1344_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_del_object(v___x_1400_);
lean_dec(v_snd_1363_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1405_);
lean_ctor_set(v___x_1408_, 1, v_next_1403_);
v_a_1350_ = v___x_1408_;
goto _start;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_dec_ref(v_next_1403_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1405_);
lean_ctor_set(v___x_1410_, 1, v_snd_1363_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1410_);
v___x_1412_ = v___x_1400_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
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
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v_a_1440_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1397_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1397_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
v___jp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_box(v_a_1368_);
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1370_);
v___x_1372_ = v___x_1365_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_snd_1363_);
v___x_1372_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
v___jp_1375_:
{
if (lean_obj_tag(v___y_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_a_1377_ = lean_ctor_get(v___y_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___y_1376_, 1);
v___x_1378_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1346_);
v___x_1379_ = l_Lean_mkAppB(v___x_1378_, v_e_1346_, v_a_1377_);
v___x_1380_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1346_, v___x_1379_, v___y_1351_, v___y_1353_, v___y_1355_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec_ref_known(v___x_1380_, 1);
v_a_1368_ = v___x_1347_;
goto v___jp_1367_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec_ref(v_e_1346_);
v_a_1389_ = lean_ctor_get(v___y_1376_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___y_1376_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___y_1376_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___y_1376_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1450_ = _args[0];
lean_object* v_a_1451_ = _args[1];
lean_object* v_e_1452_ = _args[2];
lean_object* v___x_1453_ = _args[3];
lean_object* v_a_1454_ = _args[4];
lean_object* v_a_1455_ = _args[5];
lean_object* v_a_1456_ = _args[6];
lean_object* v___y_1457_ = _args[7];
lean_object* v___y_1458_ = _args[8];
lean_object* v___y_1459_ = _args[9];
lean_object* v___y_1460_ = _args[10];
lean_object* v___y_1461_ = _args[11];
lean_object* v___y_1462_ = _args[12];
lean_object* v___y_1463_ = _args[13];
lean_object* v___y_1464_ = _args[14];
lean_object* v___y_1465_ = _args[15];
lean_object* v___y_1466_ = _args[16];
lean_object* v___y_1467_ = _args[17];
_start:
{
uint8_t v___x_138534__boxed_1468_; uint8_t v_a_138535__boxed_1469_; lean_object* v_res_1470_; 
v___x_138534__boxed_1468_ = lean_unbox(v___x_1453_);
v_a_138535__boxed_1469_ = lean_unbox(v_a_1454_);
v_res_1470_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1450_, v_a_1451_, v_e_1452_, v___x_138534__boxed_1468_, v_a_138535__boxed_1469_, v_a_1455_, v_a_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec(v___y_1457_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object* v_a_1471_, lean_object* v_a_1472_, uint8_t v_a_1473_, uint8_t v___x_1474_, lean_object* v_a_1475_, lean_object* v_e_1476_, lean_object* v_a_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v_snd_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1575_; 
v___x_1489_ = lean_st_ref_get(v___y_1478_);
v_snd_1490_ = lean_ctor_get(v_a_1477_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1477_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_a_1477_, 0);
lean_dec(v_unused_1576_);
v___x_1492_ = v_a_1477_;
v_isShared_1493_ = v_isSharedCheck_1575_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_snd_1490_);
lean_dec(v_a_1477_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1575_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v_a_1495_; lean_object* v___y_1503_; lean_object* v___x_1524_; 
lean_inc(v_snd_1490_);
v___x_1524_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1489_, v_snd_1490_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___x_1489_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1566_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1566_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1566_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_self_1529_; lean_object* v_next_1530_; uint8_t v_ctor_1531_; lean_object* v___x_1532_; 
v_self_1529_ = lean_ctor_get(v_a_1525_, 0);
lean_inc_ref(v_self_1529_);
v_next_1530_ = lean_ctor_get(v_a_1525_, 1);
lean_inc_ref(v_next_1530_);
v_ctor_1531_ = lean_ctor_get_uint8(v_a_1525_, sizeof(void*)*12 + 2);
lean_dec(v_a_1525_);
v___x_1532_ = lean_box(0);
if (v_ctor_1531_ == 0)
{
lean_dec_ref(v_self_1529_);
lean_del_object(v___x_1492_);
goto v___jp_1533_;
}
else
{
lean_object* v_self_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_self_1541_ = lean_ctor_get(v_a_1472_, 0);
v___x_1542_ = l_Lean_Expr_getAppFn(v_self_1541_);
v___x_1543_ = l_Lean_Expr_getAppFn(v_self_1529_);
v___x_1544_ = lean_expr_eqv(v___x_1542_, v___x_1543_);
lean_dec_ref(v___x_1543_);
lean_dec_ref(v___x_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_inc_ref(v_self_1529_);
lean_inc_ref(v_self_1541_);
v___x_1545_ = l_Lean_Meta_Grind_hasSameType(v_self_1541_, v_self_1529_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; uint8_t v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = lean_unbox(v_a_1546_);
lean_dec(v_a_1546_);
if (v___x_1547_ == 0)
{
lean_dec_ref(v_self_1529_);
lean_del_object(v___x_1492_);
goto v___jp_1533_;
}
else
{
lean_object* v___x_1548_; 
lean_inc_ref(v_self_1541_);
lean_dec_ref(v_next_1530_);
lean_del_object(v___x_1527_);
lean_dec_ref(v_a_1472_);
lean_inc_ref(v_a_1471_);
lean_inc_ref(v_a_1475_);
v___x_1548_ = l_Lean_Meta_mkEq(v_a_1475_, v_a_1471_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_box(v_a_1473_);
v___x_1551_ = lean_box(v___x_1474_);
v___f_1552_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1552_, 0, v_a_1475_);
lean_closure_set(v___f_1552_, 1, v_self_1541_);
lean_closure_set(v___f_1552_, 2, v_a_1471_);
lean_closure_set(v___f_1552_, 3, v_self_1529_);
lean_closure_set(v___f_1552_, 4, v___x_1550_);
lean_closure_set(v___f_1552_, 5, v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1554_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1553_, v_a_1549_, v___f_1552_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
v___y_1503_ = v___x_1554_;
goto v___jp_1502_;
}
else
{
lean_dec_ref(v_self_1541_);
lean_dec_ref(v_self_1529_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_a_1471_);
v___y_1503_ = v___x_1548_;
goto v___jp_1502_;
}
}
}
else
{
lean_dec_ref(v_self_1529_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1555_; uint8_t v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1556_ = lean_unbox(v_a_1555_);
if (v___x_1556_ == 0)
{
lean_dec(v_a_1555_);
lean_del_object(v___x_1492_);
goto v___jp_1533_;
}
else
{
uint8_t v___x_1557_; 
lean_dec_ref(v_next_1530_);
lean_del_object(v___x_1527_);
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_a_1471_);
v___x_1557_ = lean_unbox(v_a_1555_);
lean_dec(v_a_1555_);
v_a_1495_ = v___x_1557_;
goto v___jp_1494_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_next_1530_);
lean_del_object(v___x_1527_);
lean_del_object(v___x_1492_);
lean_dec(v_snd_1490_);
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_a_1471_);
v_a_1558_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1545_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1545_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_dec_ref(v_self_1529_);
lean_del_object(v___x_1492_);
goto v___jp_1533_;
}
}
v___jp_1533_:
{
uint8_t v___x_1534_; 
v___x_1534_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_1530_, v_a_1471_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_del_object(v___x_1527_);
lean_dec(v_snd_1490_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1532_);
lean_ctor_set(v___x_1535_, 1, v_next_1530_);
v___x_1536_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1471_, v_a_1472_, v_e_1476_, v___x_1474_, v_a_1473_, v_a_1475_, v___x_1535_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1536_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec_ref(v_next_1530_);
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_a_1471_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
lean_ctor_set(v___x_1537_, 1, v_snd_1490_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1537_);
v___x_1539_ = v___x_1527_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1492_);
lean_dec(v_snd_1490_);
lean_dec_ref(v_e_1476_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_a_1471_);
v_a_1567_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1524_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1524_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
v___jp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1496_ = lean_box(v_a_1495_);
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1497_);
v___x_1499_ = v___x_1492_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_snd_1490_);
v___x_1499_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
v___jp_1502_:
{
if (lean_obj_tag(v___y_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_a_1504_ = lean_ctor_get(v___y_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___y_1503_, 1);
v___x_1505_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1476_);
v___x_1506_ = l_Lean_mkAppB(v___x_1505_, v_e_1476_, v_a_1504_);
v___x_1507_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1476_, v___x_1506_, v___y_1478_, v___y_1480_, v___y_1482_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref_known(v___x_1507_, 1);
v_a_1495_ = v___x_1474_;
goto v___jp_1494_;
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_del_object(v___x_1492_);
lean_dec(v_snd_1490_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_del_object(v___x_1492_);
lean_dec(v_snd_1490_);
lean_dec_ref(v_e_1476_);
v_a_1516_ = lean_ctor_get(v___y_1503_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___y_1503_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___y_1503_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___y_1503_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_1577_ = _args[0];
lean_object* v_a_1578_ = _args[1];
lean_object* v_a_1579_ = _args[2];
lean_object* v___x_1580_ = _args[3];
lean_object* v_a_1581_ = _args[4];
lean_object* v_e_1582_ = _args[5];
lean_object* v_a_1583_ = _args[6];
lean_object* v___y_1584_ = _args[7];
lean_object* v___y_1585_ = _args[8];
lean_object* v___y_1586_ = _args[9];
lean_object* v___y_1587_ = _args[10];
lean_object* v___y_1588_ = _args[11];
lean_object* v___y_1589_ = _args[12];
lean_object* v___y_1590_ = _args[13];
lean_object* v___y_1591_ = _args[14];
lean_object* v___y_1592_ = _args[15];
lean_object* v___y_1593_ = _args[16];
lean_object* v___y_1594_ = _args[17];
_start:
{
uint8_t v_a_138768__boxed_1595_; uint8_t v___x_138769__boxed_1596_; lean_object* v_res_1597_; 
v_a_138768__boxed_1595_ = lean_unbox(v_a_1579_);
v___x_138769__boxed_1596_ = lean_unbox(v___x_1580_);
v_res_1597_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1577_, v_a_1578_, v_a_138768__boxed_1595_, v___x_138769__boxed_1596_, v_a_1581_, v_e_1582_, v_a_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(lean_object* v_a_1598_, lean_object* v_a_1599_, uint8_t v_a_1600_, uint8_t v___x_1601_, lean_object* v_e_1602_, lean_object* v_a_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v_snd_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1670_; 
v___x_1615_ = lean_st_ref_get(v___y_1604_);
v_snd_1616_ = lean_ctor_get(v_a_1603_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1603_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_a_1603_, 0);
lean_dec(v_unused_1671_);
v___x_1618_ = v_a_1603_;
v_isShared_1619_ = v_isSharedCheck_1670_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snd_1616_);
lean_dec(v_a_1603_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1670_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; 
lean_inc(v_snd_1616_);
v___x_1620_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1615_, v_snd_1616_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___x_1615_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1661_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1661_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1661_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_next_1625_; uint8_t v_ctor_1626_; lean_object* v___x_1627_; 
v_next_1625_ = lean_ctor_get(v_a_1621_, 1);
lean_inc_ref(v_next_1625_);
v_ctor_1626_ = lean_ctor_get_uint8(v_a_1621_, sizeof(void*)*12 + 2);
v___x_1627_ = lean_box(0);
if (v_ctor_1626_ == 0)
{
lean_dec(v_a_1621_);
goto v___jp_1628_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_inc_ref_n(v_a_1599_, 2);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1627_);
lean_ctor_set(v___x_1640_, 1, v_a_1599_);
lean_inc_ref(v_e_1602_);
lean_inc_ref(v_a_1598_);
v___x_1641_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1599_, v_a_1621_, v_a_1600_, v___x_1601_, v_a_1598_, v_e_1602_, v___x_1640_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1660_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1660_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1660_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_fst_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1658_; 
v_fst_1646_ = lean_ctor_get(v_a_1642_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_a_1642_, 1);
lean_dec(v_unused_1659_);
v___x_1648_ = v_a_1642_;
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_fst_1646_);
lean_dec(v_a_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
if (lean_obj_tag(v_fst_1646_) == 0)
{
lean_del_object(v___x_1648_);
lean_del_object(v___x_1644_);
goto v___jp_1628_;
}
else
{
lean_object* v_val_1650_; uint8_t v___x_1651_; 
v_val_1650_ = lean_ctor_get(v_fst_1646_, 0);
v___x_1651_ = lean_unbox(v_val_1650_);
if (v___x_1651_ == 0)
{
lean_dec_ref_known(v_fst_1646_, 1);
lean_del_object(v___x_1648_);
lean_del_object(v___x_1644_);
goto v___jp_1628_;
}
else
{
lean_object* v___x_1653_; 
lean_dec_ref(v_next_1625_);
lean_del_object(v___x_1623_);
lean_del_object(v___x_1618_);
lean_dec_ref(v_e_1602_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_a_1598_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v_snd_1616_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_fst_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_snd_1616_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1653_);
v___x_1655_ = v___x_1644_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_next_1625_);
lean_del_object(v___x_1623_);
lean_del_object(v___x_1618_);
lean_dec(v_snd_1616_);
lean_dec_ref(v_e_1602_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_a_1598_);
return v___x_1641_;
}
}
v___jp_1628_:
{
uint8_t v___x_1629_; 
v___x_1629_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_1625_, v_a_1598_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1631_; 
lean_del_object(v___x_1623_);
lean_dec(v_snd_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v_next_1625_);
lean_ctor_set(v___x_1618_, 0, v___x_1627_);
v___x_1631_ = v___x_1618_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_next_1625_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v_a_1603_ = v___x_1631_;
goto _start;
}
}
else
{
lean_object* v___x_1635_; 
lean_dec_ref(v_next_1625_);
lean_dec_ref(v_e_1602_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_a_1598_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1627_);
v___x_1635_ = v___x_1618_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_snd_1616_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1635_);
v___x_1637_ = v___x_1623_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1618_);
lean_dec(v_snd_1616_);
lean_dec_ref(v_e_1602_);
lean_dec_ref(v_a_1599_);
lean_dec_ref(v_a_1598_);
v_a_1662_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1620_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1620_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1672_ = _args[0];
lean_object* v_a_1673_ = _args[1];
lean_object* v_a_1674_ = _args[2];
lean_object* v___x_1675_ = _args[3];
lean_object* v_e_1676_ = _args[4];
lean_object* v_a_1677_ = _args[5];
lean_object* v___y_1678_ = _args[6];
lean_object* v___y_1679_ = _args[7];
lean_object* v___y_1680_ = _args[8];
lean_object* v___y_1681_ = _args[9];
lean_object* v___y_1682_ = _args[10];
lean_object* v___y_1683_ = _args[11];
lean_object* v___y_1684_ = _args[12];
lean_object* v___y_1685_ = _args[13];
lean_object* v___y_1686_ = _args[14];
lean_object* v___y_1687_ = _args[15];
lean_object* v___y_1688_ = _args[16];
_start:
{
uint8_t v_a_138988__boxed_1689_; uint8_t v___x_138989__boxed_1690_; lean_object* v_res_1691_; 
v_a_138988__boxed_1689_ = lean_unbox(v_a_1674_);
v___x_138989__boxed_1690_ = lean_unbox(v___x_1675_);
v_res_1691_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_1672_, v_a_1673_, v_a_138988__boxed_1689_, v___x_138989__boxed_1690_, v_e_1676_, v_a_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__7(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__6));
v___x_1706_ = l_Lean_mkConst(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__10(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__9));
v___x_1714_ = l_Lean_mkConst(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
lean_inc_ref(v_e_1715_);
v___x_1754_ = l_Lean_Expr_cleanupAnnotations(v_e_1715_);
v___x_1755_ = l_Lean_Expr_isApp(v___x_1754_);
if (v___x_1755_ == 0)
{
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_e_1715_);
goto v___jp_1727_;
}
else
{
lean_object* v_arg_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; 
v_arg_1756_ = lean_ctor_get(v___x_1754_, 1);
lean_inc_ref(v_arg_1756_);
v___x_1757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1754_);
v___x_1758_ = l_Lean_Expr_isApp(v___x_1757_);
if (v___x_1758_ == 0)
{
lean_dec_ref(v___x_1757_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1727_;
}
else
{
lean_object* v_arg_1759_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_arg_1759_ = lean_ctor_get(v___x_1757_, 1);
lean_inc_ref(v_arg_1759_);
v___x_1803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1757_);
v___x_1804_ = l_Lean_Expr_isApp(v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1727_;
}
else
{
lean_object* v_arg_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_arg_1805_ = lean_ctor_get(v___x_1803_, 1);
lean_inc_ref(v_arg_1805_);
v___x_1806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1803_);
v___x_1807_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_1808_ = l_Lean_Expr_isConstOf(v___x_1806_, v___x_1807_);
lean_dec_ref(v___x_1806_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1809_; 
lean_inc_ref(v_arg_1759_);
v___x_1809_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1759_, v_a_1716_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
lean_inc_ref(v_arg_1756_);
v___x_1811_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1756_, v_a_1716_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1720_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v_self_1815_; uint8_t v_ctor_1816_; lean_object* v_self_1817_; uint8_t v_ctor_1818_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; uint8_t v___y_1833_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; uint8_t v___x_1973_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v_self_1815_ = lean_ctor_get(v_a_1810_, 0);
lean_inc_ref(v_self_1815_);
v_ctor_1816_ = lean_ctor_get_uint8(v_a_1810_, sizeof(void*)*12 + 2);
lean_dec(v_a_1810_);
v_self_1817_ = lean_ctor_get(v_a_1812_, 0);
lean_inc_ref(v_self_1817_);
v_ctor_1818_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*12 + 2);
lean_dec(v_a_1812_);
v___x_1973_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1815_, v_a_1814_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; 
v___x_1974_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1817_, v_a_1814_);
if (v___x_1974_ == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1815_, v_self_1817_);
if (v___x_1975_ == 0)
{
lean_dec(v_a_1814_);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_st_ref_get(v_a_1716_);
lean_inc_ref(v_e_1715_);
v___x_1977_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1976_, v_e_1715_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; uint8_t v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_1978_, v_a_1814_);
lean_dec(v_a_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc(v_a_1719_);
lean_inc_ref(v_a_1718_);
lean_inc(v_a_1717_);
lean_inc(v_a_1716_);
lean_inc_ref(v_arg_1756_);
lean_inc_ref(v_arg_1759_);
v___x_1980_ = lean_grind_mk_eq_proof(v_arg_1759_, v_arg_1756_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
lean_inc_ref_n(v_e_1715_, 2);
v___x_1982_ = l_Lean_Meta_mkEqTrueCore(v_e_1715_, v_a_1981_);
v___x_1983_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1715_, v_a_1814_, v___x_1982_, v___x_1979_, v_a_1716_, v_a_1718_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_dec_ref_known(v___x_1983_, 1);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
else
{
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
return v___x_1983_;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1984_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1980_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1980_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_dec(v_a_1814_);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1992_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1977_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1977_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_st_ref_get(v_a_1716_);
lean_inc_ref(v_e_1715_);
v___x_2001_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2000_, v_e_1715_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v___x_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; uint8_t v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_2002_, v_self_1815_);
lean_dec(v_a_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc(v_a_1719_);
lean_inc_ref(v_a_1718_);
lean_inc(v_a_1717_);
lean_inc(v_a_1716_);
lean_inc_ref(v_arg_1756_);
v___x_2004_ = lean_grind_mk_eq_proof(v_arg_1756_, v_a_1814_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__7, &l_Lean_Meta_Grind_propagateEqUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__7);
lean_inc_ref(v_arg_1756_);
lean_inc_ref_n(v_arg_1759_, 2);
v___x_2007_ = l_Lean_mkApp3(v___x_2006_, v_arg_1759_, v_arg_1756_, v_a_2005_);
lean_inc_ref(v_e_1715_);
v___x_2008_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1715_, v_arg_1759_, v___x_2007_, v___x_2003_, v_a_1716_, v_a_1718_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_dec_ref_known(v___x_2008_, 1);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
else
{
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
return v___x_2008_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2009_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2004_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2004_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_dec(v_a_1814_);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2017_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2001_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2001_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_st_ref_get(v_a_1716_);
lean_inc_ref(v_e_1715_);
v___x_2026_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2025_, v_e_1715_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_2027_, v_self_1817_);
lean_dec(v_a_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc_ref(v_a_1722_);
lean_inc(v_a_1721_);
lean_inc_ref(v_a_1720_);
lean_inc(v_a_1719_);
lean_inc_ref(v_a_1718_);
lean_inc(v_a_1717_);
lean_inc(v_a_1716_);
lean_inc_ref(v_arg_1759_);
v___x_2029_ = lean_grind_mk_eq_proof(v_arg_1759_, v_a_1814_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__10, &l_Lean_Meta_Grind_propagateEqUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__10);
lean_inc_ref_n(v_arg_1756_, 2);
lean_inc_ref(v_arg_1759_);
v___x_2032_ = l_Lean_mkApp3(v___x_2031_, v_arg_1759_, v_arg_1756_, v_a_2030_);
lean_inc_ref(v_e_1715_);
v___x_2033_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1715_, v_arg_1756_, v___x_2032_, v___x_2028_, v_a_1716_, v_a_1718_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_dec_ref_known(v___x_2033_, 1);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
else
{
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
return v___x_2033_;
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2034_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2029_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2029_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_dec(v_a_1814_);
v___y_1865_ = v_a_1716_;
v___y_1866_ = v_a_1717_;
v___y_1867_ = v_a_1718_;
v___y_1868_ = v_a_1719_;
v___y_1869_ = v_a_1720_;
v___y_1870_ = v_a_1721_;
v___y_1871_ = v_a_1722_;
v___y_1872_ = v_a_1723_;
v___y_1873_ = v_a_1724_;
v___y_1874_ = v_a_1725_;
goto v___jp_1864_;
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2042_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2026_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2026_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
v___jp_1819_:
{
if (v___y_1833_ == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1815_, v___y_1821_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_self_1815_);
if (v___x_1834_ == 0)
{
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_self_1817_);
v___y_1761_ = v___y_1827_;
v___y_1762_ = v___y_1820_;
v___y_1763_ = v___y_1828_;
v___y_1764_ = v___y_1829_;
v___y_1765_ = v___y_1830_;
v___y_1766_ = v___y_1822_;
v___y_1767_ = v___y_1823_;
v___y_1768_ = v___y_1824_;
v___y_1769_ = v___y_1831_;
v___y_1770_ = v___y_1825_;
v___y_1771_ = v___y_1826_;
v___y_1772_ = v___x_1834_;
goto v___jp_1760_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1817_, v___y_1832_);
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_self_1817_);
v___y_1761_ = v___y_1827_;
v___y_1762_ = v___y_1820_;
v___y_1763_ = v___y_1828_;
v___y_1764_ = v___y_1829_;
v___y_1765_ = v___y_1830_;
v___y_1766_ = v___y_1822_;
v___y_1767_ = v___y_1823_;
v___y_1768_ = v___y_1824_;
v___y_1769_ = v___y_1831_;
v___y_1770_ = v___y_1825_;
v___y_1771_ = v___y_1826_;
v___y_1772_ = v___x_1835_;
goto v___jp_1760_;
}
}
else
{
lean_object* v___x_1836_; 
lean_dec_ref(v___y_1832_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_inc_ref(v_arg_1759_);
v___x_1836_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1759_, v___y_1820_, v___y_1827_, v___y_1831_, v___y_1822_, v___y_1826_, v___y_1829_, v___y_1824_, v___y_1830_, v___y_1828_, v___y_1823_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
lean_inc_ref(v_arg_1756_);
v___x_1838_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1756_, v___y_1820_, v___y_1827_, v___y_1831_, v___y_1822_, v___y_1826_, v___y_1829_, v___y_1824_, v___y_1830_, v___y_1828_, v___y_1823_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1841_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1842_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
lean_inc_ref(v___y_1825_);
v___x_1843_ = l_Lean_Name_mkStr4(v___x_1840_, v___x_1841_, v___y_1825_, v___x_1842_);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Lean_mkConst(v___x_1843_, v___x_1844_);
v___x_1846_ = l_Lean_mkApp4(v___x_1845_, v_arg_1759_, v_arg_1756_, v_a_1837_, v_a_1839_);
v___x_1847_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1715_, v___x_1846_, v___y_1820_, v___y_1831_, v___y_1826_, v___y_1824_, v___y_1830_, v___y_1828_, v___y_1823_);
return v___x_1847_;
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1837_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1848_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1838_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1838_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1856_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1836_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1836_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
v___jp_1864_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1875_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__0));
v___x_1876_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
v___x_1877_ = l_Lean_Expr_isConstOf(v_arg_1805_, v___x_1876_);
lean_dec_ref(v_arg_1805_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_inc_ref(v_e_1715_);
v___x_1878_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1715_, v___y_1865_, v___y_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1930_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1930_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1930_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_unbox(v_a_1879_);
if (v___x_1883_ == 0)
{
lean_del_object(v___x_1881_);
if (v_ctor_1816_ == 0)
{
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1751_;
}
else
{
if (v_ctor_1818_ == 0)
{
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; uint8_t v___x_1887_; 
v___x_1884_ = l_Lean_Expr_getAppFn(v_self_1815_);
v___x_1885_ = l_Lean_Expr_getAppFn(v_self_1817_);
v___x_1886_ = lean_expr_eqv(v___x_1884_, v___x_1885_);
lean_dec_ref(v___x_1885_);
lean_dec_ref(v___x_1884_);
v___x_1887_ = lean_bool_not(v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
goto v___jp_1751_;
}
else
{
lean_object* v___x_1888_; 
lean_inc_ref(v_self_1817_);
lean_inc_ref(v_self_1815_);
v___x_1888_ = l_Lean_Meta_Grind_hasSameType(v_self_1815_, v_self_1817_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; uint8_t v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = lean_unbox(v_a_1889_);
lean_dec(v_a_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
v___x_1891_ = lean_box(0);
lean_inc_ref(v_arg_1759_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v_arg_1759_);
v___x_1893_ = lean_unbox(v_a_1879_);
lean_dec(v_a_1879_);
v___x_1894_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_arg_1759_, v_arg_1756_, v___x_1893_, v___x_1808_, v_e_1715_, v___x_1892_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1903_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
v_a_1904_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1894_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1894_);
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
lean_inc_ref(v_arg_1756_);
lean_inc_ref(v_arg_1759_);
v___x_1912_ = l_Lean_Meta_mkEq(v_arg_1759_, v_arg_1756_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_box(v___x_1808_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1915_, 0, v_arg_1759_);
lean_closure_set(v___f_1915_, 1, v_self_1815_);
lean_closure_set(v___f_1915_, 2, v_arg_1756_);
lean_closure_set(v___f_1915_, 3, v_self_1817_);
lean_closure_set(v___f_1915_, 4, v_a_1879_);
lean_closure_set(v___f_1915_, 5, v___x_1914_);
v___x_1916_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1917_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1916_, v_a_1913_, v___f_1915_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
v___y_1731_ = v___y_1865_;
v___y_1732_ = v___y_1873_;
v___y_1733_ = v___y_1872_;
v___y_1734_ = v___y_1874_;
v___y_1735_ = v___y_1871_;
v___y_1736_ = v___y_1867_;
v___y_1737_ = v___y_1869_;
v___y_1738_ = v___x_1917_;
goto v___jp_1730_;
}
else
{
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
v___y_1731_ = v___y_1865_;
v___y_1732_ = v___y_1873_;
v___y_1733_ = v___y_1872_;
v___y_1734_ = v___y_1874_;
v___y_1735_ = v___y_1871_;
v___y_1736_ = v___y_1867_;
v___y_1737_ = v___y_1869_;
v___y_1738_ = v___x_1912_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1918_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1888_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1888_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec(v_a_1879_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v___x_1926_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1926_);
v___x_1928_ = v___x_1881_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1931_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1878_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1878_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v___x_1939_; 
lean_inc_ref(v_e_1715_);
v___x_1939_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1715_, v___y_1865_, v___y_1869_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; uint8_t v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_1869_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_1869_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; uint8_t v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1815_, v_a_1943_);
if (v___x_1946_ == 0)
{
v___y_1820_ = v___y_1865_;
v___y_1821_ = v_a_1945_;
v___y_1822_ = v___y_1868_;
v___y_1823_ = v___y_1874_;
v___y_1824_ = v___y_1871_;
v___y_1825_ = v___x_1875_;
v___y_1826_ = v___y_1869_;
v___y_1827_ = v___y_1866_;
v___y_1828_ = v___y_1873_;
v___y_1829_ = v___y_1870_;
v___y_1830_ = v___y_1872_;
v___y_1831_ = v___y_1867_;
v___y_1832_ = v_a_1943_;
v___y_1833_ = v___x_1946_;
goto v___jp_1819_;
}
else
{
uint8_t v___x_1947_; 
v___x_1947_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_self_1817_, v_a_1945_);
v___y_1820_ = v___y_1865_;
v___y_1821_ = v_a_1945_;
v___y_1822_ = v___y_1868_;
v___y_1823_ = v___y_1874_;
v___y_1824_ = v___y_1871_;
v___y_1825_ = v___x_1875_;
v___y_1826_ = v___y_1869_;
v___y_1827_ = v___y_1866_;
v___y_1828_ = v___y_1873_;
v___y_1829_ = v___y_1870_;
v___y_1830_ = v___y_1872_;
v___y_1831_ = v___y_1867_;
v___y_1832_ = v_a_1943_;
v___y_1833_ = v___x_1947_;
goto v___jp_1819_;
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v_a_1943_);
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1948_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1944_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1944_);
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
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1956_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1942_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1942_);
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
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
v___x_1964_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_1715_, v_arg_1759_, v_arg_1756_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1964_;
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_self_1817_);
lean_dec_ref(v_self_1815_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1965_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1939_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1939_);
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
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_1812_);
lean_dec(v_a_1810_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2050_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_1813_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_1813_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_1810_);
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2058_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1811_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1811_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_arg_1805_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_2066_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1809_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1809_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
v___jp_1760_:
{
if (v___y_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
lean_inc_ref(v_arg_1759_);
v___x_1775_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1759_, v___y_1762_, v___y_1761_, v___y_1769_, v___y_1766_, v___y_1771_, v___y_1764_, v___y_1768_, v___y_1765_, v___y_1763_, v___y_1767_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
lean_inc_ref(v_arg_1756_);
v___x_1777_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1756_, v___y_1762_, v___y_1761_, v___y_1769_, v___y_1766_, v___y_1771_, v___y_1764_, v___y_1768_, v___y_1765_, v___y_1763_, v___y_1767_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1780_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1781_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__0));
lean_inc_ref(v___y_1770_);
v___x_1782_ = l_Lean_Name_mkStr4(v___x_1779_, v___x_1780_, v___y_1770_, v___x_1781_);
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_mkConst(v___x_1782_, v___x_1783_);
v___x_1785_ = l_Lean_mkApp4(v___x_1784_, v_arg_1759_, v_arg_1756_, v_a_1776_, v_a_1778_);
v___x_1786_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1715_, v___x_1785_, v___y_1762_, v___y_1769_, v___y_1771_, v___y_1768_, v___y_1765_, v___y_1763_, v___y_1767_);
return v___x_1786_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_a_1776_);
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1787_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1777_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_arg_1759_);
lean_dec_ref(v_arg_1756_);
lean_dec_ref(v_e_1715_);
v_a_1795_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1775_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1775_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
v___jp_1730_:
{
if (lean_obj_tag(v___y_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_a_1739_ = lean_ctor_get(v___y_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___y_1738_, 1);
v___x_1740_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1715_);
v___x_1741_ = l_Lean_mkAppB(v___x_1740_, v_e_1715_, v_a_1739_);
v___x_1742_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1715_, v___x_1741_, v___y_1731_, v___y_1736_, v___y_1737_, v___y_1735_, v___y_1733_, v___y_1732_, v___y_1734_);
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_e_1715_);
v_a_1743_ = lean_ctor_get(v___y_1738_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___y_1738_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___y_1738_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___y_1738_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
v___jp_1751_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Meta_Grind_propagateEqUp(v_e_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
lean_dec(v_a_2076_);
lean_dec(v_a_2075_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object* v_00_u03b1_2087_, lean_object* v_name_2088_, uint8_t v_bi_2089_, lean_object* v_type_2090_, lean_object* v_k_2091_, uint8_t v_kind_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_2088_, v_bi_2089_, v_type_2090_, v_k_2091_, v_kind_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_2105_ = _args[0];
lean_object* v_name_2106_ = _args[1];
lean_object* v_bi_2107_ = _args[2];
lean_object* v_type_2108_ = _args[3];
lean_object* v_k_2109_ = _args[4];
lean_object* v_kind_2110_ = _args[5];
lean_object* v___y_2111_ = _args[6];
lean_object* v___y_2112_ = _args[7];
lean_object* v___y_2113_ = _args[8];
lean_object* v___y_2114_ = _args[9];
lean_object* v___y_2115_ = _args[10];
lean_object* v___y_2116_ = _args[11];
lean_object* v___y_2117_ = _args[12];
lean_object* v___y_2118_ = _args[13];
lean_object* v___y_2119_ = _args[14];
lean_object* v___y_2120_ = _args[15];
lean_object* v___y_2121_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2122_; uint8_t v_kind_boxed_2123_; lean_object* v_res_2124_; 
v_bi_boxed_2122_ = lean_unbox(v_bi_2107_);
v_kind_boxed_2123_ = lean_unbox(v_kind_2110_);
v_res_2124_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(v_00_u03b1_2105_, v_name_2106_, v_bi_boxed_2122_, v_type_2108_, v_k_2109_, v_kind_boxed_2123_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec(v___y_2111_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object* v_00_u03b1_2125_, lean_object* v_name_2126_, lean_object* v_type_2127_, lean_object* v_k_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_2126_, v_type_2127_, v_k_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_name_2142_, lean_object* v_type_2143_, lean_object* v_k_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(v_00_u03b1_2141_, v_name_2142_, v_type_2143_, v_k_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object* v_a_2157_, lean_object* v_a_2158_, uint8_t v_a_2159_, uint8_t v___x_2160_, lean_object* v_a_2161_, lean_object* v_e_2162_, lean_object* v_inst_2163_, lean_object* v_a_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_2157_, v_a_2158_, v_a_2159_, v___x_2160_, v_a_2161_, v_e_2162_, v_a_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object** _args){
lean_object* v_a_2177_ = _args[0];
lean_object* v_a_2178_ = _args[1];
lean_object* v_a_2179_ = _args[2];
lean_object* v___x_2180_ = _args[3];
lean_object* v_a_2181_ = _args[4];
lean_object* v_e_2182_ = _args[5];
lean_object* v_inst_2183_ = _args[6];
lean_object* v_a_2184_ = _args[7];
lean_object* v___y_2185_ = _args[8];
lean_object* v___y_2186_ = _args[9];
lean_object* v___y_2187_ = _args[10];
lean_object* v___y_2188_ = _args[11];
lean_object* v___y_2189_ = _args[12];
lean_object* v___y_2190_ = _args[13];
lean_object* v___y_2191_ = _args[14];
lean_object* v___y_2192_ = _args[15];
lean_object* v___y_2193_ = _args[16];
lean_object* v___y_2194_ = _args[17];
lean_object* v___y_2195_ = _args[18];
_start:
{
uint8_t v_a_139997__boxed_2196_; uint8_t v___x_139998__boxed_2197_; lean_object* v_res_2198_; 
v_a_139997__boxed_2196_ = lean_unbox(v_a_2179_);
v___x_139998__boxed_2197_ = lean_unbox(v___x_2180_);
v_res_2198_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(v_a_2177_, v_a_2178_, v_a_139997__boxed_2196_, v___x_139998__boxed_2197_, v_a_2181_, v_e_2182_, v_inst_2183_, v_a_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec(v___y_2185_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object* v_a_2199_, lean_object* v_a_2200_, uint8_t v_a_2201_, uint8_t v___x_2202_, lean_object* v_e_2203_, lean_object* v_inst_2204_, lean_object* v_a_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_2199_, v_a_2200_, v_a_2201_, v___x_2202_, v_e_2203_, v_a_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object** _args){
lean_object* v_a_2218_ = _args[0];
lean_object* v_a_2219_ = _args[1];
lean_object* v_a_2220_ = _args[2];
lean_object* v___x_2221_ = _args[3];
lean_object* v_e_2222_ = _args[4];
lean_object* v_inst_2223_ = _args[5];
lean_object* v_a_2224_ = _args[6];
lean_object* v___y_2225_ = _args[7];
lean_object* v___y_2226_ = _args[8];
lean_object* v___y_2227_ = _args[9];
lean_object* v___y_2228_ = _args[10];
lean_object* v___y_2229_ = _args[11];
lean_object* v___y_2230_ = _args[12];
lean_object* v___y_2231_ = _args[13];
lean_object* v___y_2232_ = _args[14];
lean_object* v___y_2233_ = _args[15];
lean_object* v___y_2234_ = _args[16];
lean_object* v___y_2235_ = _args[17];
_start:
{
uint8_t v_a_140050__boxed_2236_; uint8_t v___x_140051__boxed_2237_; lean_object* v_res_2238_; 
v_a_140050__boxed_2236_ = lean_unbox(v_a_2220_);
v___x_140051__boxed_2237_ = lean_unbox(v___x_2221_);
v_res_2238_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(v_a_2218_, v_a_2219_, v_a_140050__boxed_2236_, v___x_140051__boxed_2237_, v_e_2222_, v_inst_2223_, v_a_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v___y_2225_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_e_2241_, uint8_t v___x_2242_, uint8_t v_a_2243_, lean_object* v_a_2244_, lean_object* v_inst_2245_, lean_object* v_a_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_2239_, v_a_2240_, v_e_2241_, v___x_2242_, v_a_2243_, v_a_2244_, v_a_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_a_2259_ = _args[0];
lean_object* v_a_2260_ = _args[1];
lean_object* v_e_2261_ = _args[2];
lean_object* v___x_2262_ = _args[3];
lean_object* v_a_2263_ = _args[4];
lean_object* v_a_2264_ = _args[5];
lean_object* v_inst_2265_ = _args[6];
lean_object* v_a_2266_ = _args[7];
lean_object* v___y_2267_ = _args[8];
lean_object* v___y_2268_ = _args[9];
lean_object* v___y_2269_ = _args[10];
lean_object* v___y_2270_ = _args[11];
lean_object* v___y_2271_ = _args[12];
lean_object* v___y_2272_ = _args[13];
lean_object* v___y_2273_ = _args[14];
lean_object* v___y_2274_ = _args[15];
lean_object* v___y_2275_ = _args[16];
lean_object* v___y_2276_ = _args[17];
lean_object* v___y_2277_ = _args[18];
_start:
{
uint8_t v___x_140100__boxed_2278_; uint8_t v_a_140101__boxed_2279_; lean_object* v_res_2280_; 
v___x_140100__boxed_2278_ = lean_unbox(v___x_2262_);
v_a_140101__boxed_2279_ = lean_unbox(v_a_2263_);
v_res_2280_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(v_a_2259_, v_a_2260_, v_e_2261_, v___x_140100__boxed_2278_, v_a_140101__boxed_2279_, v_a_2264_, v_inst_2265_, v_a_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec(v___y_2267_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2283_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___boxed), 12, 0);
v___x_2284_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2282_, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8____boxed(lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* v_e_2287_, lean_object* v_as_2288_, size_t v_sz_2289_, size_t v_i_2290_, lean_object* v_b_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_lt(v_i_2290_, v_sz_2289_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
lean_dec_ref(v_e_2287_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_b_2291_);
return v___x_2304_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2306_; 
v_a_2305_ = lean_array_uget_borrowed(v_as_2288_, v_i_2290_);
lean_inc_ref(v_e_2287_);
lean_inc(v_a_2305_);
v___x_2306_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_a_2305_, v_e_2287_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; 
lean_dec_ref_known(v___x_2306_, 1);
v___x_2307_ = lean_box(0);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_add(v_i_2290_, v___x_2308_);
v_i_2290_ = v___x_2309_;
v_b_2291_ = v___x_2307_;
goto _start;
}
else
{
lean_dec_ref(v_e_2287_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* v_e_2311_, lean_object* v_as_2312_, lean_object* v_sz_2313_, lean_object* v_i_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
size_t v_sz_boxed_2327_; size_t v_i_boxed_2328_; lean_object* v_res_2329_; 
v_sz_boxed_2327_ = lean_unbox_usize(v_sz_2313_);
lean_dec(v_sz_2313_);
v_i_boxed_2328_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2311_, v_as_2312_, v_sz_boxed_2327_, v_i_boxed_2328_, v_b_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v_as_2312_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* v_e_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2354_; 
lean_inc_ref(v_e_2333_);
v___x_2354_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2333_, v_a_2334_, v_a_2338_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = lean_unbox(v_a_2355_);
lean_dec(v_a_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_inc_ref(v_e_2333_);
v___x_2357_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2333_, v_a_2334_, v_a_2338_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2474_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2474_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2474_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_unbox(v_a_2358_);
lean_dec(v_a_2358_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_dec_ref(v_e_2333_);
v___x_2363_ = lean_box(0);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2363_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
else
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
lean_del_object(v___x_2360_);
lean_inc_ref(v_e_2333_);
v___x_2367_ = l_Lean_Expr_cleanupAnnotations(v_e_2333_);
v___x_2368_ = l_Lean_Expr_isApp(v___x_2367_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v___x_2367_);
lean_dec_ref(v_e_2333_);
goto v___jp_2348_;
}
else
{
lean_object* v_arg_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_arg_2369_ = lean_ctor_get(v___x_2367_, 1);
lean_inc_ref(v_arg_2369_);
v___x_2370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2367_);
v___x_2371_ = l_Lean_Expr_isApp(v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec_ref(v___x_2370_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
goto v___jp_2348_;
}
else
{
lean_object* v_arg_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_arg_2372_ = lean_ctor_get(v___x_2370_, 1);
lean_inc_ref(v_arg_2372_);
v___x_2373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2370_);
v___x_2374_ = l_Lean_Expr_isApp(v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec_ref(v___x_2373_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
goto v___jp_2348_;
}
else
{
lean_object* v_arg_2375_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; uint8_t v___y_2387_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_arg_2375_ = lean_ctor_get(v___x_2373_, 1);
lean_inc_ref(v_arg_2375_);
v___x_2468_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2373_);
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2470_ = l_Lean_Expr_isConstOf(v___x_2468_, v___x_2469_);
lean_dec_ref(v___x_2468_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
goto v___jp_2348_;
}
else
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
v___x_2472_ = l_Lean_Expr_isConstOf(v_arg_2375_, v___x_2471_);
if (v___x_2472_ == 0)
{
v___y_2411_ = v_a_2334_;
v___y_2412_ = v_a_2335_;
v___y_2413_ = v_a_2336_;
v___y_2414_ = v_a_2337_;
v___y_2415_ = v_a_2338_;
v___y_2416_ = v_a_2339_;
v___y_2417_ = v_a_2340_;
v___y_2418_ = v_a_2341_;
v___y_2419_ = v_a_2342_;
v___y_2420_ = v_a_2343_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2473_; 
lean_inc_ref(v_arg_2369_);
lean_inc_ref(v_arg_2372_);
lean_inc_ref(v_e_2333_);
v___x_2473_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_2333_, v_arg_2372_, v_arg_2369_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_dec_ref_known(v___x_2473_, 1);
v___y_2411_ = v_a_2334_;
v___y_2412_ = v_a_2335_;
v___y_2413_ = v_a_2336_;
v___y_2414_ = v_a_2337_;
v___y_2415_ = v_a_2338_;
v___y_2416_ = v_a_2339_;
v___y_2417_ = v_a_2340_;
v___y_2418_ = v_a_2341_;
v___y_2419_ = v_a_2342_;
v___y_2420_ = v_a_2343_;
goto v___jp_2410_;
}
else
{
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
return v___x_2473_;
}
}
}
v___jp_2376_:
{
if (v___y_2387_ == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2375_, v___y_2382_, v___y_2379_, v___y_2378_, v___y_2377_, v___y_2386_, v___y_2383_, v___y_2385_, v___y_2380_, v___y_2384_, v___y_2381_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_box(0);
v_sz_2391_ = lean_array_size(v_a_2389_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2333_, v_a_2389_, v_sz_2391_, v___x_2392_, v___x_2390_, v___y_2382_, v___y_2379_, v___y_2378_, v___y_2377_, v___y_2386_, v___y_2383_, v___y_2385_, v___y_2380_, v___y_2384_, v___y_2381_);
lean_dec(v_a_2389_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; 
v_unused_2401_ = lean_ctor_get(v___x_2393_, 0);
lean_dec(v_unused_2401_);
v___x_2395_ = v___x_2393_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_dec(v___x_2393_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2390_);
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2390_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
else
{
return v___x_2393_;
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v_e_2333_);
v_a_2402_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2388_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2388_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_e_2333_);
goto v___jp_2345_;
}
}
v___jp_2410_:
{
lean_object* v___x_2421_; 
lean_inc_ref(v_arg_2369_);
lean_inc_ref(v_arg_2372_);
v___x_2421_ = l_Lean_Meta_Grind_Solvers_propagateDiseqs(v_arg_2372_, v_arg_2369_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v___x_2422_; 
lean_dec_ref_known(v___x_2421_, 1);
lean_inc_ref(v_arg_2375_);
v___x_2422_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2375_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2459_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2459_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2459_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2427_ = lean_array_get_size(v_a_2423_);
lean_dec(v_a_2423_);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_nat_dec_eq(v___x_2427_, v___x_2428_);
v___x_2430_ = lean_bool_not(v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
v___x_2431_ = lean_box(0);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2431_);
v___x_2433_ = v___x_2425_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v___x_2435_; 
lean_del_object(v___x_2425_);
v___x_2435_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2372_, v___y_2411_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2369_, v___y_2411_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
v___x_2440_ = l_Lean_Expr_isAppOf(v_arg_2375_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec(v_a_2438_);
lean_dec(v_a_2436_);
v___y_2377_ = v___y_2414_;
v___y_2378_ = v___y_2413_;
v___y_2379_ = v___y_2412_;
v___y_2380_ = v___y_2418_;
v___y_2381_ = v___y_2420_;
v___y_2382_ = v___y_2411_;
v___y_2383_ = v___y_2416_;
v___y_2384_ = v___y_2419_;
v___y_2385_ = v___y_2417_;
v___y_2386_ = v___y_2415_;
v___y_2387_ = v___x_2440_;
goto v___jp_2376_;
}
else
{
uint8_t v_ctor_2441_; 
v_ctor_2441_ = lean_ctor_get_uint8(v_a_2436_, sizeof(void*)*12 + 2);
lean_dec(v_a_2436_);
if (v_ctor_2441_ == 0)
{
uint8_t v_ctor_2442_; 
v_ctor_2442_ = lean_ctor_get_uint8(v_a_2438_, sizeof(void*)*12 + 2);
lean_dec(v_a_2438_);
v___y_2377_ = v___y_2414_;
v___y_2378_ = v___y_2413_;
v___y_2379_ = v___y_2412_;
v___y_2380_ = v___y_2418_;
v___y_2381_ = v___y_2420_;
v___y_2382_ = v___y_2411_;
v___y_2383_ = v___y_2416_;
v___y_2384_ = v___y_2419_;
v___y_2385_ = v___y_2417_;
v___y_2386_ = v___y_2415_;
v___y_2387_ = v_ctor_2442_;
goto v___jp_2376_;
}
else
{
lean_dec(v_a_2438_);
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_e_2333_);
goto v___jp_2345_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_e_2333_);
v_a_2443_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2437_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2437_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
v_a_2451_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2435_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2435_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
v_a_2460_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2422_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2422_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2375_);
lean_dec_ref(v_arg_2372_);
lean_dec_ref(v_arg_2369_);
lean_dec_ref(v_e_2333_);
return v___x_2421_;
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
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_e_2333_);
v_a_2475_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2357_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2357_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
else
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
lean_inc_ref(v_e_2333_);
v___x_2483_ = l_Lean_Expr_cleanupAnnotations(v_e_2333_);
v___x_2484_ = l_Lean_Expr_isApp(v___x_2483_);
if (v___x_2484_ == 0)
{
lean_dec_ref(v___x_2483_);
lean_dec_ref(v_e_2333_);
goto v___jp_2351_;
}
else
{
lean_object* v_arg_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_arg_2485_ = lean_ctor_get(v___x_2483_, 1);
lean_inc_ref(v_arg_2485_);
v___x_2486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2483_);
v___x_2487_ = l_Lean_Expr_isApp(v___x_2486_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v___x_2486_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
goto v___jp_2351_;
}
else
{
lean_object* v_arg_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_arg_2488_ = lean_ctor_get(v___x_2486_, 1);
lean_inc_ref(v_arg_2488_);
v___x_2489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2486_);
v___x_2490_ = l_Lean_Expr_isApp(v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v___x_2489_);
lean_dec_ref(v_arg_2488_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
goto v___jp_2351_;
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2489_);
v___x_2492_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2493_ = l_Lean_Expr_isConstOf(v___x_2491_, v___x_2492_);
lean_dec_ref(v___x_2491_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v_arg_2488_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
goto v___jp_2351_;
}
else
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2488_, v_arg_2485_, v_a_2334_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2517_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2517_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2517_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_unbox(v_a_2495_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
lean_del_object(v___x_2497_);
lean_inc_ref(v_e_2333_);
v___x_2500_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2333_, v_a_2501_);
v___x_2503_ = lean_unbox(v_a_2495_);
lean_dec(v_a_2495_);
v___x_2504_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2488_, v_arg_2485_, v___x_2502_, v___x_2503_, v_a_2334_, v_a_2336_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2504_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2495_);
lean_dec_ref(v_arg_2488_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
v_a_2505_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2500_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2500_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v_a_2495_);
lean_dec_ref(v_arg_2488_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
v___x_2513_ = lean_box(0);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2513_);
v___x_2515_ = v___x_2497_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_arg_2488_);
lean_dec_ref(v_arg_2485_);
lean_dec_ref(v_e_2333_);
v_a_2518_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2494_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2494_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
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
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_e_2333_);
v_a_2526_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2354_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2354_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
v___jp_2345_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
v___jp_2348_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
v___jp_2351_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Meta_Grind_propagateEqDown(v_e_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_a_2535_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2549_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown___boxed), 12, 0);
v___x_2550_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2548_, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8____boxed(lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object* v_u_2556_, lean_object* v_00_u03b1_2557_, lean_object* v_binst_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1));
v___x_2565_ = l_Lean_mkConst(v___x_2564_, v_u_2556_);
v___x_2566_ = l_Lean_mkAppB(v___x_2565_, v_00_u03b1_2557_, v_binst_2558_);
v___x_2567_ = lean_box(0);
v___x_2568_ = l_Lean_Meta_synthInstance_x3f(v___x_2566_, v___x_2567_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object* v_u_2569_, lean_object* v_00_u03b1_2570_, lean_object* v_binst_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2569_, v_00_u03b1_2570_, v_binst_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object* v_u_2578_, lean_object* v_00_u03b1_2579_, lean_object* v_binst_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2578_, v_00_u03b1_2579_, v_binst_2580_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object* v_u_2593_, lean_object* v_00_u03b1_2594_, lean_object* v_binst_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(v_u_2593_, v_00_u03b1_2594_, v_binst_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec(v_a_2596_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* v_e_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
lean_inc_ref(v_e_2623_);
v___x_2638_ = l_Lean_Expr_cleanupAnnotations(v_e_2623_);
v___x_2639_ = l_Lean_Expr_isApp(v___x_2638_);
if (v___x_2639_ == 0)
{
lean_dec_ref(v___x_2638_);
lean_dec_ref(v_e_2623_);
goto v___jp_2635_;
}
else
{
lean_object* v_arg_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_arg_2640_ = lean_ctor_get(v___x_2638_, 1);
lean_inc_ref(v_arg_2640_);
v___x_2641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2638_);
v___x_2642_ = l_Lean_Expr_isApp(v___x_2641_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v___x_2641_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
goto v___jp_2635_;
}
else
{
lean_object* v_arg_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_arg_2643_ = lean_ctor_get(v___x_2641_, 1);
lean_inc_ref(v_arg_2643_);
v___x_2644_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2641_);
v___x_2645_ = l_Lean_Expr_isApp(v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v___x_2644_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
goto v___jp_2635_;
}
else
{
lean_object* v_arg_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_arg_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc_ref(v_arg_2646_);
v___x_2647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2644_);
v___x_2648_ = l_Lean_Expr_isApp(v___x_2647_);
if (v___x_2648_ == 0)
{
lean_dec_ref(v___x_2647_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
goto v___jp_2635_;
}
else
{
lean_object* v_arg_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_arg_2649_ = lean_ctor_get(v___x_2647_, 1);
lean_inc_ref(v_arg_2649_);
v___x_2650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2647_);
v___x_2651_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2652_ = l_Lean_Expr_isConstOf(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_dec_ref(v___x_2650_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
goto v___jp_2635_;
}
else
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2643_, v_arg_2640_, v_a_2624_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v_u_2655_; uint8_t v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
v_u_2655_ = l_Lean_Expr_constLevels_x21(v___x_2650_);
lean_dec_ref(v___x_2650_);
v___x_2656_ = lean_unbox(v_a_2654_);
lean_dec(v_a_2654_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_inc_ref(v_arg_2640_);
lean_inc_ref(v_arg_2643_);
v___x_2657_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_arg_2643_, v_arg_2640_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2690_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2690_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2690_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
if (lean_obj_tag(v_a_2658_) == 1)
{
lean_object* v_val_2662_; lean_object* v___x_2663_; 
lean_del_object(v___x_2660_);
v_val_2662_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_a_2658_, 1);
lean_inc_ref(v_arg_2646_);
lean_inc_ref(v_arg_2649_);
lean_inc(v_u_2655_);
v___x_2663_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2655_, v_arg_2649_, v_arg_2646_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2677_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
if (lean_obj_tag(v_a_2664_) == 1)
{
lean_object* v_val_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_del_object(v___x_2666_);
v_val_2668_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v_a_2664_, 1);
v___x_2669_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
v___x_2670_ = l_Lean_mkConst(v___x_2669_, v_u_2655_);
v___x_2671_ = l_Lean_mkApp6(v___x_2670_, v_arg_2649_, v_arg_2646_, v_val_2668_, v_arg_2643_, v_arg_2640_, v_val_2662_);
v___x_2672_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_2623_, v___x_2671_, v_a_2624_, v_a_2626_, v_a_2628_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
lean_dec(v_a_2664_);
lean_dec(v_val_2662_);
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v___x_2673_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2673_);
v___x_2675_ = v___x_2666_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_val_2662_);
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v_a_2678_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2663_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2663_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_dec(v_a_2658_);
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v___x_2686_ = lean_box(0);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2686_);
v___x_2688_ = v___x_2660_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v_a_2691_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2657_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2657_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v___x_2699_; 
lean_inc_ref(v_arg_2646_);
lean_inc_ref(v_arg_2649_);
lean_inc(v_u_2655_);
v___x_2699_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2655_, v_arg_2649_, v_arg_2646_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2723_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2723_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2723_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
if (lean_obj_tag(v_a_2700_) == 1)
{
lean_object* v_val_2704_; lean_object* v___x_2705_; 
lean_del_object(v___x_2702_);
v_val_2704_ = lean_ctor_get(v_a_2700_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v_a_2700_, 1);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
lean_inc_ref(v_a_2630_);
lean_inc(v_a_2629_);
lean_inc_ref(v_a_2628_);
lean_inc(v_a_2627_);
lean_inc_ref(v_a_2626_);
lean_inc(v_a_2625_);
lean_inc(v_a_2624_);
lean_inc_ref(v_arg_2640_);
lean_inc_ref(v_arg_2643_);
v___x_2705_ = lean_grind_mk_eq_proof(v_arg_2643_, v_arg_2640_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v___x_2707_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
v___x_2708_ = l_Lean_mkConst(v___x_2707_, v_u_2655_);
v___x_2709_ = l_Lean_mkApp6(v___x_2708_, v_arg_2649_, v_arg_2646_, v_val_2704_, v_arg_2643_, v_arg_2640_, v_a_2706_);
v___x_2710_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_2623_, v___x_2709_, v_a_2624_, v_a_2626_, v_a_2628_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
return v___x_2710_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_val_2704_);
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v_a_2711_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2705_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2705_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec(v_a_2700_);
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v___x_2719_ = lean_box(0);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2719_);
v___x_2721_ = v___x_2702_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_u_2655_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v_a_2724_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2699_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2699_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v___x_2650_);
lean_dec_ref(v_arg_2649_);
lean_dec_ref(v_arg_2646_);
lean_dec_ref(v_arg_2643_);
lean_dec_ref(v_arg_2640_);
lean_dec_ref(v_e_2623_);
v_a_2732_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2653_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2653_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object* v_e_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_Grind_propagateBEqUp(v_e_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec(v_a_2741_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp___boxed), 12, 0);
v___x_2756_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2754_, v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8____boxed(lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object* v_e_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2784_; uint8_t v___x_2785_; 
lean_inc_ref(v_e_2769_);
v___x_2784_ = l_Lean_Expr_cleanupAnnotations(v_e_2769_);
v___x_2785_ = l_Lean_Expr_isApp(v___x_2784_);
if (v___x_2785_ == 0)
{
lean_dec_ref(v___x_2784_);
lean_dec_ref(v_e_2769_);
goto v___jp_2781_;
}
else
{
lean_object* v_arg_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_arg_2786_ = lean_ctor_get(v___x_2784_, 1);
lean_inc_ref(v_arg_2786_);
v___x_2787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2784_);
v___x_2788_ = l_Lean_Expr_isApp(v___x_2787_);
if (v___x_2788_ == 0)
{
lean_dec_ref(v___x_2787_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
goto v___jp_2781_;
}
else
{
lean_object* v_arg_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_arg_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc_ref(v_arg_2789_);
v___x_2790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2787_);
v___x_2791_ = l_Lean_Expr_isApp(v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec_ref(v___x_2790_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
goto v___jp_2781_;
}
else
{
lean_object* v_arg_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v_arg_2792_ = lean_ctor_get(v___x_2790_, 1);
lean_inc_ref(v_arg_2792_);
v___x_2793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2790_);
v___x_2794_ = l_Lean_Expr_isApp(v___x_2793_);
if (v___x_2794_ == 0)
{
lean_dec_ref(v___x_2793_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
goto v___jp_2781_;
}
else
{
lean_object* v_arg_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_arg_2795_ = lean_ctor_get(v___x_2793_, 1);
lean_inc_ref(v_arg_2795_);
v___x_2796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2793_);
v___x_2797_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2798_ = l_Lean_Expr_isConstOf(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
goto v___jp_2781_;
}
else
{
lean_object* v___x_2799_; 
lean_inc_ref(v_e_2769_);
v___x_2799_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_2769_, v_a_2770_, v_a_2774_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v_u_2801_; uint8_t v___x_2802_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v_u_2801_ = l_Lean_Expr_constLevels_x21(v___x_2796_);
lean_dec_ref(v___x_2796_);
v___x_2802_ = lean_unbox(v_a_2800_);
lean_dec(v_a_2800_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
lean_inc_ref(v_e_2769_);
v___x_2803_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_2769_, v_a_2770_, v_a_2774_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2886_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2886_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2886_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
uint8_t v___x_2808_; 
v___x_2808_ = lean_unbox(v_a_2804_);
lean_dec(v_a_2804_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v___x_2809_ = lean_box(0);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2809_);
v___x_2811_ = v___x_2806_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
else
{
lean_object* v___x_2813_; 
lean_del_object(v___x_2806_);
lean_inc_ref(v_arg_2792_);
lean_inc_ref(v_arg_2795_);
lean_inc(v_u_2801_);
v___x_2813_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2801_, v_arg_2795_, v_arg_2792_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2877_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2877_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2877_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
if (lean_obj_tag(v_a_2814_) == 1)
{
lean_object* v_val_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_del_object(v___x_2816_);
v_val_2818_ = lean_ctor_get(v_a_2814_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v_a_2814_, 1);
v___x_2819_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2820_ = lean_box(0);
v___x_2821_ = l_List_head_x21___redArg(v___x_2820_, v_u_2801_);
v___x_2822_ = l_Lean_Level_succ___override(v___x_2821_);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_mkConst(v___x_2819_, v___x_2824_);
lean_inc_ref(v_arg_2786_);
lean_inc_ref(v_arg_2789_);
lean_inc_ref(v_arg_2795_);
v___x_2826_ = l_Lean_mkApp3(v___x_2825_, v_arg_2795_, v_arg_2789_, v_arg_2786_);
v___x_2827_ = l_Lean_Meta_Sym_shareCommon(v___x_2826_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_2789_, v_a_2770_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = lean_box(0);
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc(v_a_2828_);
v___x_2832_ = lean_grind_internalize(v_a_2828_, v_a_2830_, v___x_2831_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2833_; 
lean_dec_ref_known(v___x_2832_, 1);
v___x_2833_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2774_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
v___x_2835_ = lean_grind_mk_eq_proof(v_e_2769_, v_a_2834_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
v___x_2838_ = l_Lean_mkConst(v___x_2837_, v_u_2801_);
v___x_2839_ = l_Lean_mkApp6(v___x_2838_, v_arg_2795_, v_arg_2792_, v_val_2818_, v_arg_2789_, v_arg_2786_, v_a_2836_);
v___x_2840_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_2828_, v___x_2839_, v_a_2770_, v_a_2772_, v_a_2774_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2840_;
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2828_);
lean_dec(v_val_2818_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
v_a_2841_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2835_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2835_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v_a_2828_);
lean_dec(v_val_2818_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2849_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2833_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2833_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_dec(v_a_2828_);
lean_dec(v_val_2818_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
return v___x_2832_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_a_2828_);
lean_dec(v_val_2818_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2857_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2829_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2829_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_val_2818_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2865_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2827_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2827_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_dec(v_a_2814_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v___x_2873_ = lean_box(0);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2873_);
v___x_2875_ = v___x_2816_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2878_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2813_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2813_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2887_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2803_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2803_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v___x_2895_; 
lean_inc_ref(v_arg_2792_);
lean_inc_ref(v_arg_2795_);
lean_inc(v_u_2801_);
v___x_2895_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2801_, v_arg_2795_, v_arg_2792_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2930_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2930_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2930_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
if (lean_obj_tag(v_a_2896_) == 1)
{
lean_object* v_val_2900_; lean_object* v___x_2901_; 
lean_del_object(v___x_2898_);
v_val_2900_ = lean_ctor_get(v_a_2896_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v_a_2896_, 1);
v___x_2901_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2774_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc(v_a_2777_);
lean_inc_ref(v_a_2776_);
lean_inc(v_a_2775_);
lean_inc_ref(v_a_2774_);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
v___x_2903_ = lean_grind_mk_eq_proof(v_e_2769_, v_a_2902_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
v___x_2906_ = l_Lean_mkConst(v___x_2905_, v_u_2801_);
lean_inc_ref(v_arg_2786_);
lean_inc_ref(v_arg_2789_);
v___x_2907_ = l_Lean_mkApp6(v___x_2906_, v_arg_2795_, v_arg_2792_, v_val_2900_, v_arg_2789_, v_arg_2786_, v_a_2904_);
v___x_2908_ = 0;
v___x_2909_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2789_, v_arg_2786_, v___x_2907_, v___x_2908_, v_a_2770_, v_a_2772_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_val_2900_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
v_a_2910_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2903_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2903_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_val_2900_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2918_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2901_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2901_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
lean_dec(v_a_2896_);
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v___x_2926_ = lean_box(0);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2926_);
v___x_2928_ = v___x_2898_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_u_2801_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2931_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2895_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2895_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_arg_2795_);
lean_dec_ref(v_arg_2792_);
lean_dec_ref(v_arg_2789_);
lean_dec_ref(v_arg_2786_);
lean_dec_ref(v_e_2769_);
v_a_2939_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2799_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2799_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
}
}
}
v___jp_2781_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object* v_e_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Meta_Grind_propagateBEqDown(v_e_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec(v_a_2948_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2962_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqDown___boxed), 12, 0);
v___x_2963_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2961_, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8____boxed(lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* v_e_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2986_; 
lean_inc_ref(v_e_2971_);
v___x_2986_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2971_, v_a_2972_, v_a_2976_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3024_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3024_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3024_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_unbox(v_a_2987_);
lean_dec(v_a_2987_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_dec_ref(v_e_2971_);
v___x_2992_ = lean_box(0);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
lean_del_object(v___x_2989_);
lean_inc_ref(v_e_2971_);
v___x_2996_ = l_Lean_Expr_cleanupAnnotations(v_e_2971_);
v___x_2997_ = l_Lean_Expr_isApp(v___x_2996_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v___x_2996_);
lean_dec_ref(v_e_2971_);
goto v___jp_2983_;
}
else
{
lean_object* v_arg_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_arg_2998_ = lean_ctor_get(v___x_2996_, 1);
lean_inc_ref(v_arg_2998_);
v___x_2999_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2996_);
v___x_3000_ = l_Lean_Expr_isApp(v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v___x_2999_);
lean_dec_ref(v_arg_2998_);
lean_dec_ref(v_e_2971_);
goto v___jp_2983_;
}
else
{
lean_object* v_arg_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_arg_3001_ = lean_ctor_get(v___x_2999_, 1);
lean_inc_ref(v_arg_3001_);
v___x_3002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2999_);
v___x_3003_ = l_Lean_Expr_isApp(v___x_3002_);
if (v___x_3003_ == 0)
{
lean_dec_ref(v___x_3002_);
lean_dec_ref(v_arg_3001_);
lean_dec_ref(v_arg_2998_);
lean_dec_ref(v_e_2971_);
goto v___jp_2983_;
}
else
{
lean_object* v_arg_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_arg_3004_ = lean_ctor_get(v___x_3002_, 1);
lean_inc_ref(v_arg_3004_);
v___x_3005_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3002_);
v___x_3006_ = l_Lean_Expr_isApp(v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec_ref(v___x_3005_);
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3001_);
lean_dec_ref(v_arg_2998_);
lean_dec_ref(v_e_2971_);
goto v___jp_2983_;
}
else
{
lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3005_);
v___x_3008_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3009_ = l_Lean_Expr_isConstOf(v___x_3007_, v___x_3008_);
lean_dec_ref(v___x_3007_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3001_);
lean_dec_ref(v_arg_2998_);
lean_dec_ref(v_e_2971_);
goto v___jp_2983_;
}
else
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_arg_2998_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref_known(v___x_3010_, 1);
lean_inc_ref(v_e_2971_);
v___x_3011_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2971_, v_a_3012_);
v___x_3014_ = 0;
v___x_3015_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3004_, v_arg_3001_, v___x_3013_, v___x_3014_, v_a_2972_, v_a_2974_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
return v___x_3015_;
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3001_);
lean_dec_ref(v_e_2971_);
v_a_3016_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3011_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3011_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3001_);
lean_dec_ref(v_e_2971_);
return v___x_3010_;
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
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_e_2971_);
v_a_3025_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2986_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2986_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
v___jp_2983_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object* v_e_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Meta_Grind_propagateEqMatchDown(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3048_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown___boxed), 12, 0);
v___x_3049_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3047_, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8____boxed(lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* v_e_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3070_; 
lean_inc_ref(v_e_3055_);
v___x_3070_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3055_, v_a_3056_, v_a_3060_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3105_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3105_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3105_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_unbox(v_a_3071_);
lean_dec(v_a_3071_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec_ref(v_e_3055_);
v___x_3076_ = lean_box(0);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3076_);
v___x_3078_ = v___x_3073_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
else
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
lean_del_object(v___x_3073_);
lean_inc_ref(v_e_3055_);
v___x_3080_ = l_Lean_Expr_cleanupAnnotations(v_e_3055_);
v___x_3081_ = l_Lean_Expr_isApp(v___x_3080_);
if (v___x_3081_ == 0)
{
lean_dec_ref(v___x_3080_);
lean_dec_ref(v_e_3055_);
goto v___jp_3067_;
}
else
{
lean_object* v_arg_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v_arg_3082_ = lean_ctor_get(v___x_3080_, 1);
lean_inc_ref(v_arg_3082_);
v___x_3083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3080_);
v___x_3084_ = l_Lean_Expr_isApp(v___x_3083_);
if (v___x_3084_ == 0)
{
lean_dec_ref(v___x_3083_);
lean_dec_ref(v_arg_3082_);
lean_dec_ref(v_e_3055_);
goto v___jp_3067_;
}
else
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3083_);
v___x_3086_ = l_Lean_Expr_isApp(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v___x_3085_);
lean_dec_ref(v_arg_3082_);
lean_dec_ref(v_e_3055_);
goto v___jp_3067_;
}
else
{
lean_object* v_arg_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_arg_3087_ = lean_ctor_get(v___x_3085_, 1);
lean_inc_ref(v_arg_3087_);
v___x_3088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3085_);
v___x_3089_ = l_Lean_Expr_isApp(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_arg_3082_);
lean_dec_ref(v_e_3055_);
goto v___jp_3067_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3088_);
v___x_3091_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3092_ = l_Lean_Expr_isConstOf(v___x_3090_, v___x_3091_);
lean_dec_ref(v___x_3090_);
if (v___x_3092_ == 0)
{
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_arg_3082_);
lean_dec_ref(v_e_3055_);
goto v___jp_3067_;
}
else
{
lean_object* v___x_3093_; 
lean_inc_ref(v_e_3055_);
v___x_3093_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3095_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3055_, v_a_3094_);
v___x_3096_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3087_, v_arg_3082_, v___x_3095_, v___x_3092_, v_a_3056_, v_a_3058_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_arg_3082_);
lean_dec_ref(v_e_3055_);
v_a_3097_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3093_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3093_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
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
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v_e_3055_);
v_a_3106_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3070_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3070_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
v___jp_3067_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object* v_e_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_Grind_propagateHEqDown(v_e_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
lean_dec(v_a_3116_);
lean_dec(v_a_3115_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3129_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown___boxed), 12, 0);
v___x_3130_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3128_, v___x_3129_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8____boxed(lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* v_e_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v___x_3148_; uint8_t v___x_3149_; 
lean_inc_ref(v_e_3133_);
v___x_3148_ = l_Lean_Expr_cleanupAnnotations(v_e_3133_);
v___x_3149_ = l_Lean_Expr_isApp(v___x_3148_);
if (v___x_3149_ == 0)
{
lean_dec_ref(v___x_3148_);
lean_dec_ref(v_e_3133_);
goto v___jp_3145_;
}
else
{
lean_object* v_arg_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v_arg_3150_ = lean_ctor_get(v___x_3148_, 1);
lean_inc_ref(v_arg_3150_);
v___x_3151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3148_);
v___x_3152_ = l_Lean_Expr_isApp(v___x_3151_);
if (v___x_3152_ == 0)
{
lean_dec_ref(v___x_3151_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3151_);
v___x_3154_ = l_Lean_Expr_isApp(v___x_3153_);
if (v___x_3154_ == 0)
{
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
goto v___jp_3145_;
}
else
{
lean_object* v_arg_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_arg_3155_ = lean_ctor_get(v___x_3153_, 1);
lean_inc_ref(v_arg_3155_);
v___x_3156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3153_);
v___x_3157_ = l_Lean_Expr_isApp(v___x_3156_);
if (v___x_3157_ == 0)
{
lean_dec_ref(v___x_3156_);
lean_dec_ref(v_arg_3155_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3156_);
v___x_3159_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3160_ = l_Lean_Expr_isConstOf(v___x_3158_, v___x_3159_);
lean_dec_ref(v___x_3158_);
if (v___x_3160_ == 0)
{
lean_dec_ref(v_arg_3155_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_3155_, v_arg_3150_, v_a_3134_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3183_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3183_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3183_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_unbox(v_a_3162_);
lean_dec(v_a_3162_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_dec_ref(v_arg_3155_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
v___x_3167_ = lean_box(0);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3167_);
v___x_3169_ = v___x_3164_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
else
{
lean_object* v___x_3171_; 
lean_del_object(v___x_3164_);
lean_inc(v_a_3143_);
lean_inc_ref(v_a_3142_);
lean_inc(v_a_3141_);
lean_inc_ref(v_a_3140_);
lean_inc(v_a_3139_);
lean_inc_ref(v_a_3138_);
lean_inc(v_a_3137_);
lean_inc_ref(v_a_3136_);
lean_inc(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3171_ = lean_grind_mk_heq_proof(v_arg_3155_, v_arg_3150_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
lean_inc_ref(v_e_3133_);
v___x_3173_ = l_Lean_Meta_mkEqTrueCore(v_e_3133_, v_a_3172_);
v___x_3174_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3133_, v___x_3173_, v_a_3134_, v_a_3136_, v_a_3138_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3174_;
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_e_3133_);
v_a_3175_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3171_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3171_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_arg_3155_);
lean_dec_ref(v_arg_3150_);
lean_dec_ref(v_e_3133_);
v_a_3184_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3161_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3161_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
}
}
v___jp_3145_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object* v_e_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Lean_Meta_Grind_propagateHEqUp(v_e_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec(v_a_3193_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3207_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp___boxed), 12, 0);
v___x_3208_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3206_, v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8____boxed(lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object* v_e_3211_, lean_object* v_args_3212_, uint8_t v_ite_3213_, lean_object* v_rhs_3214_, lean_object* v_h_3215_, lean_object* v_i_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = lean_array_get_size(v_args_3212_);
v___x_3229_ = lean_nat_dec_lt(v_i_3216_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; 
lean_dec(v_i_3216_);
v___x_3230_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_rhs_3214_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3211_, v_a_3217_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
lean_inc_ref(v_e_3211_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_e_3211_);
lean_inc(v_a_3226_);
lean_inc_ref(v_a_3225_);
lean_inc(v_a_3224_);
lean_inc_ref(v_a_3223_);
lean_inc(v_a_3222_);
lean_inc_ref(v_a_3221_);
lean_inc(v_a_3220_);
lean_inc_ref(v_a_3219_);
lean_inc(v_a_3218_);
lean_inc(v_a_3217_);
lean_inc(v_a_3231_);
v___x_3235_ = lean_grind_internalize(v_a_3231_, v_a_3233_, v___x_3234_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec_ref_known(v___x_3235_, 1);
if (v_ite_3213_ == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3211_, v_a_3231_, v_h_3215_, v___x_3229_, v_a_3217_, v_a_3219_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; 
lean_inc(v_a_3231_);
lean_inc_ref(v_e_3211_);
v___x_3237_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3211_, v_a_3231_, v_a_3217_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref_known(v___x_3237_, 1);
v___x_3238_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3211_, v_a_3231_, v_h_3215_, v___x_3229_, v_a_3217_, v_a_3219_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3238_;
}
else
{
lean_dec(v_a_3231_);
lean_dec_ref(v_h_3215_);
lean_dec_ref(v_e_3211_);
return v___x_3237_;
}
}
}
else
{
lean_dec(v_a_3231_);
lean_dec_ref(v_h_3215_);
lean_dec_ref(v_e_3211_);
return v___x_3235_;
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v_a_3231_);
lean_dec_ref(v_h_3215_);
lean_dec_ref(v_e_3211_);
v_a_3239_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3232_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3232_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_h_3215_);
lean_dec_ref(v_e_3211_);
v_a_3247_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3230_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3230_);
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
lean_object* v_arg_3255_; lean_object* v_rhs_x27_3256_; lean_object* v___x_3257_; 
v_arg_3255_ = lean_array_fget_borrowed(v_args_3212_, v_i_3216_);
lean_inc_n(v_arg_3255_, 2);
v_rhs_x27_3256_ = l_Lean_Expr_app___override(v_rhs_3214_, v_arg_3255_);
v___x_3257_ = l_Lean_Meta_mkCongrFun(v_h_3215_, v_arg_3255_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___x_3259_ = lean_unsigned_to_nat(1u);
v___x_3260_ = lean_nat_add(v_i_3216_, v___x_3259_);
lean_dec(v_i_3216_);
v_rhs_3214_ = v_rhs_x27_3256_;
v_h_3215_ = v_a_3258_;
v_i_3216_ = v___x_3260_;
goto _start;
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_rhs_x27_3256_);
lean_dec(v_i_3216_);
lean_dec_ref(v_e_3211_);
v_a_3262_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3257_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3257_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object** _args){
lean_object* v_e_3270_ = _args[0];
lean_object* v_args_3271_ = _args[1];
lean_object* v_ite_3272_ = _args[2];
lean_object* v_rhs_3273_ = _args[3];
lean_object* v_h_3274_ = _args[4];
lean_object* v_i_3275_ = _args[5];
lean_object* v_a_3276_ = _args[6];
lean_object* v_a_3277_ = _args[7];
lean_object* v_a_3278_ = _args[8];
lean_object* v_a_3279_ = _args[9];
lean_object* v_a_3280_ = _args[10];
lean_object* v_a_3281_ = _args[11];
lean_object* v_a_3282_ = _args[12];
lean_object* v_a_3283_ = _args[13];
lean_object* v_a_3284_ = _args[14];
lean_object* v_a_3285_ = _args[15];
lean_object* v_a_3286_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3287_; lean_object* v_res_3288_; 
v_ite_boxed_3287_ = lean_unbox(v_ite_3272_);
v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3270_, v_args_3271_, v_ite_boxed_3287_, v_rhs_3273_, v_h_3274_, v_i_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
lean_dec(v_a_3281_);
lean_dec_ref(v_a_3280_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_args_3271_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object* v_e_3289_, lean_object* v_rhs_3290_, lean_object* v_h_3291_, lean_object* v_prefixSize_3292_, lean_object* v_args_3293_, uint8_t v_ite_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3315_ = lean_array_get_size(v_args_3293_);
v___x_3316_ = lean_nat_dec_eq(v_prefixSize_3292_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3289_, v_args_3293_, v_ite_3294_, v_rhs_3290_, v_h_3291_, v_prefixSize_3292_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
return v___x_3317_;
}
else
{
lean_object* v___x_3318_; 
lean_dec(v_prefixSize_3292_);
v___x_3318_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3289_, v_a_3295_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
lean_inc_ref(v_e_3289_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_e_3289_);
lean_inc(v_a_3304_);
lean_inc_ref(v_a_3303_);
lean_inc(v_a_3302_);
lean_inc_ref(v_a_3301_);
lean_inc(v_a_3300_);
lean_inc_ref(v_a_3299_);
lean_inc(v_a_3298_);
lean_inc_ref(v_a_3297_);
lean_inc(v_a_3296_);
lean_inc(v_a_3295_);
lean_inc_ref(v_rhs_3290_);
v___x_3321_ = lean_grind_internalize(v_rhs_3290_, v_a_3319_, v___x_3320_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_dec_ref_known(v___x_3321_, 1);
if (v_ite_3294_ == 0)
{
v___y_3307_ = v_a_3295_;
v___y_3308_ = v_a_3297_;
v___y_3309_ = v_a_3301_;
v___y_3310_ = v_a_3302_;
v___y_3311_ = v_a_3303_;
v___y_3312_ = v_a_3304_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3322_; 
lean_inc_ref(v_rhs_3290_);
lean_inc_ref(v_e_3289_);
v___x_3322_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3289_, v_rhs_3290_, v_a_3295_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref_known(v___x_3322_, 1);
v___y_3307_ = v_a_3295_;
v___y_3308_ = v_a_3297_;
v___y_3309_ = v_a_3301_;
v___y_3310_ = v_a_3302_;
v___y_3311_ = v_a_3303_;
v___y_3312_ = v_a_3304_;
goto v___jp_3306_;
}
else
{
lean_dec_ref(v_h_3291_);
lean_dec_ref(v_rhs_3290_);
lean_dec_ref(v_e_3289_);
return v___x_3322_;
}
}
}
else
{
lean_dec_ref(v_h_3291_);
lean_dec_ref(v_rhs_3290_);
lean_dec_ref(v_e_3289_);
return v___x_3321_;
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v_h_3291_);
lean_dec_ref(v_rhs_3290_);
lean_dec_ref(v_e_3289_);
v_a_3323_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3318_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3318_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
v___jp_3306_:
{
uint8_t v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = 0;
v___x_3314_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3289_, v_rhs_3290_, v_h_3291_, v___x_3313_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
return v___x_3314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object** _args){
lean_object* v_e_3331_ = _args[0];
lean_object* v_rhs_3332_ = _args[1];
lean_object* v_h_3333_ = _args[2];
lean_object* v_prefixSize_3334_ = _args[3];
lean_object* v_args_3335_ = _args[4];
lean_object* v_ite_3336_ = _args[5];
lean_object* v_a_3337_ = _args[6];
lean_object* v_a_3338_ = _args[7];
lean_object* v_a_3339_ = _args[8];
lean_object* v_a_3340_ = _args[9];
lean_object* v_a_3341_ = _args[10];
lean_object* v_a_3342_ = _args[11];
lean_object* v_a_3343_ = _args[12];
lean_object* v_a_3344_ = _args[13];
lean_object* v_a_3345_ = _args[14];
lean_object* v_a_3346_ = _args[15];
lean_object* v_a_3347_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3348_; lean_object* v_res_3349_; 
v_ite_boxed_3348_ = lean_unbox(v_ite_3336_);
v_res_3349_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3331_, v_rhs_3332_, v_h_3333_, v_prefixSize_3334_, v_args_3335_, v_ite_boxed_3348_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_args_3335_);
return v_res_3349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateIte___closed__0(void){
_start:
{
lean_object* v___x_3350_; lean_object* v_dummy_3351_; 
v___x_3350_ = lean_box(0);
v_dummy_3351_ = l_Lean_Expr_sort___override(v___x_3350_);
return v_dummy_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* v_e_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_numArgs_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_numArgs_3370_ = l_Lean_Expr_getAppNumArgs(v_e_3358_);
v___x_3371_ = lean_unsigned_to_nat(5u);
v___x_3372_ = lean_nat_dec_lt(v_numArgs_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v_c_3376_; lean_object* v___x_3377_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_sub(v_numArgs_3370_, v___x_3373_);
v___x_3375_ = lean_nat_sub(v___x_3374_, v___x_3373_);
v_c_3376_ = l_Lean_Expr_getRevArg_x21(v_e_3358_, v___x_3375_);
lean_inc_ref(v_c_3376_);
v___x_3377_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3376_, v_a_3359_, v_a_3363_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; uint8_t v___x_3379_; uint8_t v___x_3380_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = 1;
v___x_3380_ = lean_unbox(v_a_3378_);
lean_dec(v_a_3378_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
lean_inc_ref(v_c_3376_);
v___x_3381_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3376_, v_a_3359_, v_a_3363_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3415_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3415_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3415_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_unbox(v_a_3382_);
lean_dec(v_a_3382_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
lean_dec_ref(v_c_3376_);
lean_dec(v___x_3374_);
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v___x_3387_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3387_);
v___x_3389_ = v___x_3384_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
else
{
lean_object* v___x_3391_; 
lean_del_object(v___x_3384_);
v___x_3391_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3376_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v_dummy_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = l_Lean_Expr_getAppFn(v_e_3358_);
v___x_3394_ = l_Lean_instInhabitedExpr;
v_dummy_3395_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3396_ = lean_mk_array(v_numArgs_3370_, v_dummy_3395_);
lean_inc_ref(v_e_3358_);
v___x_3397_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3358_, v___x_3396_, v___x_3374_);
v___x_3398_ = lean_unsigned_to_nat(4u);
v___x_3399_ = lean_array_get(v___x_3394_, v___x_3397_, v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
v___x_3401_ = l_Lean_Expr_constLevels_x21(v___x_3393_);
lean_dec_ref(v___x_3393_);
v___x_3402_ = l_Lean_mkConst(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = l_Lean_mkAppRange(v___x_3402_, v___x_3403_, v___x_3371_, v___x_3397_);
v___x_3405_ = l_Lean_Expr_app___override(v___x_3404_, v_a_3392_);
v___x_3406_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3358_, v___x_3399_, v___x_3405_, v___x_3371_, v___x_3397_, v___x_3379_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref(v___x_3397_);
return v___x_3406_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v___x_3374_);
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v_a_3407_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3391_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3391_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v_c_3376_);
lean_dec(v___x_3374_);
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v_a_3416_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3381_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3381_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3376_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_dummy_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = l_Lean_Expr_getAppFn(v_e_3358_);
v___x_3427_ = l_Lean_instInhabitedExpr;
v_dummy_3428_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3429_ = lean_mk_array(v_numArgs_3370_, v_dummy_3428_);
lean_inc_ref(v_e_3358_);
v___x_3430_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3358_, v___x_3429_, v___x_3374_);
v___x_3431_ = lean_unsigned_to_nat(3u);
v___x_3432_ = lean_array_get(v___x_3427_, v___x_3430_, v___x_3431_);
v___x_3433_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__4));
v___x_3434_ = l_Lean_Expr_constLevels_x21(v___x_3426_);
lean_dec_ref(v___x_3426_);
v___x_3435_ = l_Lean_mkConst(v___x_3433_, v___x_3434_);
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = l_Lean_mkAppRange(v___x_3435_, v___x_3436_, v___x_3371_, v___x_3430_);
v___x_3438_ = l_Lean_Expr_app___override(v___x_3437_, v_a_3425_);
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3358_, v___x_3432_, v___x_3438_, v___x_3371_, v___x_3430_, v___x_3379_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref(v___x_3430_);
return v___x_3439_;
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v___x_3374_);
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v_a_3440_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3424_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3424_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v_c_3376_);
lean_dec(v___x_3374_);
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v_a_3448_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3377_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3377_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v_numArgs_3370_);
lean_dec_ref(v_e_3358_);
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object* v_e_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_Meta_Grind_propagateIte(v_e_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec(v_a_3459_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_));
v___x_3476_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte___boxed), 12, 0);
v___x_3477_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3475_, v___x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8____boxed(lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_();
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* v_e_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v_numArgs_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_numArgs_3502_ = l_Lean_Expr_getAppNumArgs(v_e_3490_);
v___x_3503_ = lean_unsigned_to_nat(5u);
v___x_3504_ = lean_nat_dec_lt(v_numArgs_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_c_3508_; lean_object* v___x_3509_; 
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = lean_nat_sub(v_numArgs_3502_, v___x_3505_);
v___x_3507_ = lean_nat_sub(v___x_3506_, v___x_3505_);
v_c_3508_ = l_Lean_Expr_getRevArg_x21(v_e_3490_, v___x_3507_);
lean_inc_ref(v_c_3508_);
v___x_3509_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3508_, v_a_3491_, v_a_3495_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; uint8_t v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = lean_unbox(v_a_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_inc_ref(v_c_3508_);
v___x_3512_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3508_, v_a_3491_, v_a_3495_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3570_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3570_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3570_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
uint8_t v___x_3517_; 
v___x_3517_ = lean_unbox(v_a_3513_);
lean_dec(v_a_3513_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
lean_dec(v_a_3510_);
lean_dec_ref(v_c_3508_);
lean_dec(v___x_3506_);
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v___x_3518_ = lean_box(0);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3518_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
else
{
lean_object* v___x_3522_; 
lean_del_object(v___x_3515_);
lean_inc_ref(v_c_3508_);
v___x_3522_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3508_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v_dummy_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_n(v_a_3523_, 2);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = l_Lean_Expr_getAppFn(v_e_3490_);
v_dummy_3525_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3526_ = lean_mk_array(v_numArgs_3502_, v_dummy_3525_);
lean_inc_ref(v_e_3490_);
v___x_3527_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3490_, v___x_3526_, v___x_3506_);
v___x_3528_ = l_Lean_instInhabitedExpr;
v___x_3529_ = lean_unsigned_to_nat(4u);
v___x_3530_ = lean_array_get(v___x_3528_, v___x_3527_, v___x_3529_);
v___x_3531_ = l_Lean_Meta_mkOfEqFalseCore(v_c_3508_, v_a_3523_);
v___x_3532_ = l_Lean_Expr_app___override(v___x_3530_, v___x_3531_);
lean_inc(v_a_3500_);
lean_inc_ref(v_a_3499_);
lean_inc(v_a_3498_);
lean_inc_ref(v_a_3497_);
lean_inc(v_a_3496_);
lean_inc_ref(v_a_3495_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc(v_a_3491_);
v___x_3533_ = lean_grind_preprocess(v___x_3532_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v_expr_3535_; lean_object* v___x_3536_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v_expr_3535_ = lean_ctor_get(v_a_3534_, 0);
lean_inc_ref(v_expr_3535_);
v___x_3536_ = l_Lean_Meta_Simp_Result_getProof(v_a_3534_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
v___x_3539_ = l_Lean_Expr_constLevels_x21(v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3540_ = l_Lean_mkConst(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = l_Lean_mkAppRange(v___x_3540_, v___x_3541_, v___x_3503_, v___x_3527_);
lean_inc_ref(v_expr_3535_);
v___x_3543_ = l_Lean_mkApp3(v___x_3542_, v_expr_3535_, v_a_3523_, v_a_3537_);
v___x_3544_ = lean_unbox(v_a_3510_);
lean_dec(v_a_3510_);
v___x_3545_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3490_, v_expr_3535_, v___x_3543_, v___x_3503_, v___x_3527_, v___x_3544_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
lean_dec_ref(v___x_3527_);
return v___x_3545_;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v_expr_3535_);
lean_dec_ref(v___x_3527_);
lean_dec_ref(v___x_3524_);
lean_dec(v_a_3523_);
lean_dec(v_a_3510_);
lean_dec_ref(v_e_3490_);
v_a_3546_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3536_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3536_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v___x_3527_);
lean_dec_ref(v___x_3524_);
lean_dec(v_a_3523_);
lean_dec(v_a_3510_);
lean_dec_ref(v_e_3490_);
v_a_3554_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3533_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3533_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_a_3510_);
lean_dec_ref(v_c_3508_);
lean_dec(v___x_3506_);
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v_a_3562_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3522_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3522_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_a_3510_);
lean_dec_ref(v_c_3508_);
lean_dec(v___x_3506_);
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v_a_3571_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3512_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3512_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v___x_3579_; 
lean_dec(v_a_3510_);
lean_inc_ref(v_c_3508_);
v___x_3579_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3508_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; lean_object* v_dummy_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc_n(v_a_3580_, 2);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3581_ = l_Lean_Expr_getAppFn(v_e_3490_);
v_dummy_3582_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3583_ = lean_mk_array(v_numArgs_3502_, v_dummy_3582_);
lean_inc_ref(v_e_3490_);
v___x_3584_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3490_, v___x_3583_, v___x_3506_);
v___x_3585_ = l_Lean_instInhabitedExpr;
v___x_3586_ = lean_unsigned_to_nat(3u);
v___x_3587_ = lean_array_get(v___x_3585_, v___x_3584_, v___x_3586_);
v___x_3588_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3508_, v_a_3580_);
v___x_3589_ = l_Lean_Expr_app___override(v___x_3587_, v___x_3588_);
lean_inc(v_a_3500_);
lean_inc_ref(v_a_3499_);
lean_inc(v_a_3498_);
lean_inc_ref(v_a_3497_);
lean_inc(v_a_3496_);
lean_inc_ref(v_a_3495_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc(v_a_3491_);
v___x_3590_ = lean_grind_preprocess(v___x_3589_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v_expr_3592_; lean_object* v___x_3593_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v_expr_3592_ = lean_ctor_get(v_a_3591_, 0);
lean_inc_ref(v_expr_3592_);
v___x_3593_ = l_Lean_Meta_Simp_Result_getProof(v_a_3591_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__3));
v___x_3596_ = l_Lean_Expr_constLevels_x21(v___x_3581_);
lean_dec_ref(v___x_3581_);
v___x_3597_ = l_Lean_mkConst(v___x_3595_, v___x_3596_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v___x_3599_ = l_Lean_mkAppRange(v___x_3597_, v___x_3598_, v___x_3503_, v___x_3584_);
lean_inc_ref(v_expr_3592_);
v___x_3600_ = l_Lean_mkApp3(v___x_3599_, v_expr_3592_, v_a_3580_, v_a_3594_);
v___x_3601_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3490_, v_expr_3592_, v___x_3600_, v___x_3503_, v___x_3584_, v___x_3504_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
lean_dec_ref(v___x_3584_);
return v___x_3601_;
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v_expr_3592_);
lean_dec_ref(v___x_3584_);
lean_dec_ref(v___x_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_e_3490_);
v_a_3602_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3593_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3593_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v___x_3584_);
lean_dec_ref(v___x_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_e_3490_);
v_a_3610_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3590_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3590_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_c_3508_);
lean_dec(v___x_3506_);
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v_a_3618_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3579_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3579_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec_ref(v_c_3508_);
lean_dec(v___x_3506_);
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v_a_3626_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3509_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3509_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec(v_numArgs_3502_);
lean_dec_ref(v_e_3490_);
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object* v_e_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_Meta_Grind_propagateDIte(v_e_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec(v_a_3637_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_));
v___x_3654_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte___boxed), 12, 0);
v___x_3655_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3653_, v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8____boxed(lean_object* v_a_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_();
return v_res_3657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = lean_box(0);
v___x_3677_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__8));
v___x_3678_ = l_Lean_mkConst(v___x_3677_, v___x_3676_);
return v___x_3678_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = lean_box(0);
v___x_3685_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__11));
v___x_3686_ = l_Lean_mkConst(v___x_3685_, v___x_3684_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* v_e_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v___x_3702_; 
lean_inc_ref(v_e_3687_);
v___x_3702_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_3687_, v_a_3688_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3756_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3756_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3756_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
uint8_t v_ctor_3707_; 
v_ctor_3707_ = lean_ctor_get_uint8(v_a_3703_, sizeof(void*)*12 + 2);
if (v_ctor_3707_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec(v_a_3703_);
lean_dec_ref(v_e_3687_);
v___x_3708_ = lean_box(0);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3708_);
v___x_3710_ = v___x_3705_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
else
{
lean_object* v_self_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_self_3712_ = lean_ctor_get(v_a_3703_, 0);
lean_inc_ref(v_self_3712_);
lean_dec(v_a_3703_);
lean_inc_ref(v_e_3687_);
v___x_3713_ = l_Lean_Expr_cleanupAnnotations(v_e_3687_);
v___x_3714_ = l_Lean_Expr_isApp(v___x_3713_);
if (v___x_3714_ == 0)
{
lean_dec_ref(v___x_3713_);
lean_dec_ref(v_self_3712_);
lean_del_object(v___x_3705_);
lean_dec_ref(v_e_3687_);
goto v___jp_3699_;
}
else
{
lean_object* v_arg_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_arg_3715_ = lean_ctor_get(v___x_3713_, 1);
lean_inc_ref(v_arg_3715_);
v___x_3716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3713_);
v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_dec_ref(v___x_3716_);
lean_dec_ref(v_arg_3715_);
lean_dec_ref(v_self_3712_);
lean_del_object(v___x_3705_);
lean_dec_ref(v_e_3687_);
goto v___jp_3699_;
}
else
{
lean_object* v_arg_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v_arg_3718_ = lean_ctor_get(v___x_3716_, 1);
lean_inc_ref(v_arg_3718_);
v___x_3719_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3716_);
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3721_ = l_Lean_Expr_isConstOf(v___x_3719_, v___x_3720_);
lean_dec_ref(v___x_3719_);
if (v___x_3721_ == 0)
{
lean_dec_ref(v_arg_3718_);
lean_dec_ref(v_arg_3715_);
lean_dec_ref(v_self_3712_);
lean_del_object(v___x_3705_);
lean_dec_ref(v_e_3687_);
goto v___jp_3699_;
}
else
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
v___x_3723_ = l_Lean_Expr_isConstOf(v_self_3712_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
v___x_3725_ = l_Lean_Expr_isConstOf(v_self_3712_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec_ref(v_arg_3718_);
lean_dec_ref(v_arg_3715_);
lean_dec_ref(v_self_3712_);
lean_dec_ref(v_e_3687_);
v___x_3726_ = lean_box(0);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3726_);
v___x_3728_ = v___x_3705_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
else
{
lean_object* v___x_3730_; 
lean_del_object(v___x_3705_);
lean_inc(v_a_3697_);
lean_inc_ref(v_a_3696_);
lean_inc(v_a_3695_);
lean_inc_ref(v_a_3694_);
lean_inc(v_a_3693_);
lean_inc_ref(v_a_3692_);
lean_inc(v_a_3691_);
lean_inc_ref(v_a_3690_);
lean_inc(v_a_3689_);
lean_inc(v_a_3688_);
v___x_3730_ = lean_grind_mk_eq_proof(v_e_3687_, v_self_3712_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__9, &l_Lean_Meta_Grind_propagateDecideDown___closed__9_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9);
lean_inc_ref(v_arg_3718_);
v___x_3733_ = l_Lean_mkApp3(v___x_3732_, v_arg_3718_, v_arg_3715_, v_a_3731_);
v___x_3734_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_3718_, v___x_3733_, v_a_3688_, v_a_3690_, v_a_3692_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
return v___x_3734_;
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec_ref(v_arg_3718_);
lean_dec_ref(v_arg_3715_);
v_a_3735_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3730_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3730_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
else
{
lean_object* v___x_3743_; 
lean_del_object(v___x_3705_);
lean_inc(v_a_3697_);
lean_inc_ref(v_a_3696_);
lean_inc(v_a_3695_);
lean_inc_ref(v_a_3694_);
lean_inc(v_a_3693_);
lean_inc_ref(v_a_3692_);
lean_inc(v_a_3691_);
lean_inc_ref(v_a_3690_);
lean_inc(v_a_3689_);
lean_inc(v_a_3688_);
v___x_3743_ = lean_grind_mk_eq_proof(v_e_3687_, v_self_3712_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__12, &l_Lean_Meta_Grind_propagateDecideDown___closed__12_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12);
lean_inc_ref(v_arg_3718_);
v___x_3746_ = l_Lean_mkApp3(v___x_3745_, v_arg_3718_, v_arg_3715_, v_a_3744_);
v___x_3747_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_3718_, v___x_3746_, v_a_3688_, v_a_3690_, v_a_3692_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
return v___x_3747_;
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v_arg_3718_);
lean_dec_ref(v_arg_3715_);
v_a_3748_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3743_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3743_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
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
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec_ref(v_e_3687_);
v_a_3757_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3702_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3702_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
v___jp_3699_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_box(0);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object* v_e_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_Meta_Grind_propagateDecideDown(v_e_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec(v_a_3766_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3779_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3780_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown___boxed), 12, 0);
v___x_3781_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3779_, v___x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8____boxed(lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
return v_res_3783_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = lean_box(0);
v___x_3790_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__1));
v___x_3791_ = l_Lean_mkConst(v___x_3790_, v___x_3789_);
return v___x_3791_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_box(0);
v___x_3798_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__4));
v___x_3799_ = l_Lean_mkConst(v___x_3798_, v___x_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* v_e_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v___x_3815_; uint8_t v___x_3816_; 
lean_inc_ref(v_e_3800_);
v___x_3815_ = l_Lean_Expr_cleanupAnnotations(v_e_3800_);
v___x_3816_ = l_Lean_Expr_isApp(v___x_3815_);
if (v___x_3816_ == 0)
{
lean_dec_ref(v___x_3815_);
lean_dec_ref(v_e_3800_);
goto v___jp_3812_;
}
else
{
lean_object* v_arg_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v_arg_3817_ = lean_ctor_get(v___x_3815_, 1);
lean_inc_ref(v_arg_3817_);
v___x_3818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3815_);
v___x_3819_ = l_Lean_Expr_isApp(v___x_3818_);
if (v___x_3819_ == 0)
{
lean_dec_ref(v___x_3818_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
goto v___jp_3812_;
}
else
{
lean_object* v_arg_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_arg_3820_ = lean_ctor_get(v___x_3818_, 1);
lean_inc_ref(v_arg_3820_);
v___x_3821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3818_);
v___x_3822_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3823_ = l_Lean_Expr_isConstOf(v___x_3821_, v___x_3822_);
lean_dec_ref(v___x_3821_);
if (v___x_3823_ == 0)
{
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
goto v___jp_3812_;
}
else
{
lean_object* v___x_3824_; 
lean_inc_ref(v_arg_3820_);
v___x_3824_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_3820_, v_a_3801_, v_a_3805_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; uint8_t v___x_3826_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = lean_unbox(v_a_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
lean_inc_ref(v_arg_3820_);
v___x_3827_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_3820_, v_a_3801_, v_a_3805_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3861_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3861_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3861_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
uint8_t v___x_3832_; 
v___x_3832_ = lean_unbox(v_a_3828_);
lean_dec(v_a_3828_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_dec(v_a_3825_);
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v___x_3833_ = lean_box(0);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3833_);
v___x_3835_ = v___x_3830_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
else
{
lean_object* v___x_3837_; 
lean_del_object(v___x_3830_);
v___x_3837_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3805_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
lean_inc_ref(v_arg_3820_);
v___x_3839_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_3820_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__2, &l_Lean_Meta_Grind_propagateDecideUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2);
v___x_3842_ = l_Lean_mkApp3(v___x_3841_, v_arg_3820_, v_arg_3817_, v_a_3840_);
v___x_3843_ = lean_unbox(v_a_3825_);
lean_dec(v_a_3825_);
v___x_3844_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3800_, v_a_3838_, v___x_3842_, v___x_3843_, v_a_3801_, v_a_3803_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_3844_;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_a_3838_);
lean_dec(v_a_3825_);
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3845_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3839_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3839_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_a_3825_);
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3853_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3837_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3837_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_a_3825_);
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3862_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3827_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3827_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v___x_3870_; 
lean_dec(v_a_3825_);
v___x_3870_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3805_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
lean_inc_ref(v_arg_3820_);
v___x_3872_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_3820_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v___x_3874_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__5, &l_Lean_Meta_Grind_propagateDecideUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5);
v___x_3875_ = l_Lean_mkApp3(v___x_3874_, v_arg_3820_, v_arg_3817_, v_a_3873_);
v___x_3876_ = 0;
v___x_3877_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3800_, v_a_3871_, v___x_3875_, v___x_3876_, v_a_3801_, v_a_3803_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_a_3871_);
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3878_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3872_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3872_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3886_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3870_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3870_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_dec_ref(v_arg_3820_);
lean_dec_ref(v_arg_3817_);
lean_dec_ref(v_e_3800_);
v_a_3894_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3824_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3824_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
}
v___jp_3812_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_Grind_propagateDecideUp(v_e_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec(v_a_3903_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp___boxed), 12, 0);
v___x_3918_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3916_, v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8____boxed(lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
return v_res_3920_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3930_ = lean_box(0);
v___x_3931_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__2));
v___x_3932_ = l_Lean_mkConst(v___x_3931_, v___x_3930_);
return v___x_3932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_box(0);
v___x_3939_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__4));
v___x_3940_ = l_Lean_mkConst(v___x_3939_, v___x_3938_);
return v___x_3940_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7(void){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3946_ = lean_box(0);
v___x_3947_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__6));
v___x_3948_ = l_Lean_mkConst(v___x_3947_, v___x_3946_);
return v___x_3948_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9(void){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__8));
v___x_3956_ = l_Lean_mkConst(v___x_3955_, v___x_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* v_e_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3972_; uint8_t v___x_3973_; 
lean_inc_ref(v_e_3957_);
v___x_3972_ = l_Lean_Expr_cleanupAnnotations(v_e_3957_);
v___x_3973_ = l_Lean_Expr_isApp(v___x_3972_);
if (v___x_3973_ == 0)
{
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_e_3957_);
goto v___jp_3969_;
}
else
{
lean_object* v_arg_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v_arg_3974_ = lean_ctor_get(v___x_3972_, 1);
lean_inc_ref(v_arg_3974_);
v___x_3975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3972_);
v___x_3976_ = l_Lean_Expr_isApp(v___x_3975_);
if (v___x_3976_ == 0)
{
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
goto v___jp_3969_;
}
else
{
lean_object* v_arg_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v_arg_3977_ = lean_ctor_get(v___x_3975_, 1);
lean_inc_ref(v_arg_3977_);
v___x_3978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3975_);
v___x_3979_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_3980_ = l_Lean_Expr_isConstOf(v___x_3978_, v___x_3979_);
lean_dec_ref(v___x_3978_);
if (v___x_3980_ == 0)
{
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
goto v___jp_3969_;
}
else
{
lean_object* v___x_3981_; 
lean_inc_ref(v_arg_3977_);
v___x_3981_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3977_, v_a_3958_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = lean_unbox(v_a_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
lean_inc_ref(v_arg_3974_);
v___x_3984_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3974_, v_a_3958_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; uint8_t v___x_3986_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = lean_unbox(v_a_3985_);
lean_dec(v_a_3985_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec(v_a_3982_);
lean_inc_ref(v_arg_3977_);
v___x_3987_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3977_, v_a_3958_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = lean_unbox(v_a_3988_);
lean_dec(v_a_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
lean_inc_ref(v_arg_3974_);
v___x_3990_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3974_, v_a_3958_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4013_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4013_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4013_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
uint8_t v___x_3995_; 
v___x_3995_ = lean_unbox(v_a_3991_);
lean_dec(v_a_3991_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v___x_3996_ = lean_box(0);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3996_);
v___x_3998_ = v___x_3993_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
else
{
lean_object* v___x_4000_; 
lean_del_object(v___x_3993_);
lean_inc_ref(v_arg_3974_);
v___x_4000_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3974_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v___x_4002_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__3, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3);
v___x_4003_ = l_Lean_mkApp3(v___x_4002_, v_arg_3977_, v_arg_3974_, v_a_4001_);
v___x_4004_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3957_, v___x_4003_, v_a_3958_, v_a_3960_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_4004_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4005_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_4000_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4000_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4014_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3990_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3990_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_object* v___x_4022_; 
lean_inc_ref(v_arg_3977_);
v___x_4022_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3977_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
v___x_4024_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__5, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5);
v___x_4025_ = l_Lean_mkApp3(v___x_4024_, v_arg_3977_, v_arg_3974_, v_a_4023_);
v___x_4026_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3957_, v___x_4025_, v_a_3958_, v_a_3960_, v_a_3962_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_4026_;
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4027_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4022_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4022_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4035_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_3987_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_3987_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_object* v___x_4043_; 
lean_inc_ref(v_arg_3974_);
v___x_4043_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3974_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v___x_4043_, 1);
v___x_4045_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__7, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7);
lean_inc_ref(v_arg_3977_);
v___x_4046_ = l_Lean_mkApp3(v___x_4045_, v_arg_3977_, v_arg_3974_, v_a_4044_);
v___x_4047_ = lean_unbox(v_a_3982_);
lean_dec(v_a_3982_);
v___x_4048_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3957_, v_arg_3977_, v___x_4046_, v___x_4047_, v_a_3958_, v_a_3960_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_4048_;
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_3982_);
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4049_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4043_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4043_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_3982_);
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4057_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_3984_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_3984_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v___x_4065_; 
lean_dec(v_a_3982_);
lean_inc_ref(v_arg_3977_);
v___x_4065_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3977_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4065_, 1);
v___x_4067_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__9, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9);
lean_inc_ref(v_arg_3974_);
v___x_4068_ = l_Lean_mkApp3(v___x_4067_, v_arg_3977_, v_arg_3974_, v_a_4066_);
v___x_4069_ = 0;
v___x_4070_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3957_, v_arg_3974_, v___x_4068_, v___x_4069_, v_a_3958_, v_a_3960_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
return v___x_4070_;
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4071_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4065_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4065_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v_arg_3977_);
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3957_);
v_a_4079_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_3981_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_3981_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
}
v___jp_3969_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_box(0);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object* v_e_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_Grind_propagateBoolAndUp(v_e_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec(v_a_4088_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4102_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp___boxed), 12, 0);
v___x_4103_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4101_, v___x_4102_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8____boxed(lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
return v_res_4105_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4111_ = lean_box(0);
v___x_4112_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__0));
v___x_4113_ = l_Lean_mkConst(v___x_4112_, v___x_4111_);
return v___x_4113_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4119_ = lean_box(0);
v___x_4120_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__2));
v___x_4121_ = l_Lean_mkConst(v___x_4120_, v___x_4119_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* v_e_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4137_; 
lean_inc_ref(v_e_4122_);
v___x_4137_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4122_, v_a_4123_, v_a_4127_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4172_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4172_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4172_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
uint8_t v___x_4142_; 
v___x_4142_ = lean_unbox(v_a_4138_);
lean_dec(v_a_4138_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; lean_object* v___x_4145_; 
lean_dec_ref(v_e_4122_);
v___x_4143_ = lean_box(0);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4143_);
v___x_4145_ = v___x_4140_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
else
{
lean_object* v___x_4147_; uint8_t v___x_4148_; 
lean_del_object(v___x_4140_);
lean_inc_ref(v_e_4122_);
v___x_4147_ = l_Lean_Expr_cleanupAnnotations(v_e_4122_);
v___x_4148_ = l_Lean_Expr_isApp(v___x_4147_);
if (v___x_4148_ == 0)
{
lean_dec_ref(v___x_4147_);
lean_dec_ref(v_e_4122_);
goto v___jp_4134_;
}
else
{
lean_object* v_arg_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v_arg_4149_ = lean_ctor_get(v___x_4147_, 1);
lean_inc_ref(v_arg_4149_);
v___x_4150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4147_);
v___x_4151_ = l_Lean_Expr_isApp(v___x_4150_);
if (v___x_4151_ == 0)
{
lean_dec_ref(v___x_4150_);
lean_dec_ref(v_arg_4149_);
lean_dec_ref(v_e_4122_);
goto v___jp_4134_;
}
else
{
lean_object* v_arg_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; 
v_arg_4152_ = lean_ctor_get(v___x_4150_, 1);
lean_inc_ref(v_arg_4152_);
v___x_4153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4150_);
v___x_4154_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4155_ = l_Lean_Expr_isConstOf(v___x_4153_, v___x_4154_);
lean_dec_ref(v___x_4153_);
if (v___x_4155_ == 0)
{
lean_dec_ref(v_arg_4152_);
lean_dec_ref(v_arg_4149_);
lean_dec_ref(v_e_4122_);
goto v___jp_4134_;
}
else
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc_n(v_a_4157_, 2);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__1, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1);
lean_inc_ref(v_arg_4149_);
lean_inc_ref_n(v_arg_4152_, 2);
v___x_4159_ = l_Lean_mkApp3(v___x_4158_, v_arg_4152_, v_arg_4149_, v_a_4157_);
v___x_4160_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4152_, v___x_4159_, v_a_4123_, v_a_4125_, v_a_4127_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref_known(v___x_4160_, 1);
v___x_4161_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__3, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3);
lean_inc_ref(v_arg_4149_);
v___x_4162_ = l_Lean_mkApp3(v___x_4161_, v_arg_4152_, v_arg_4149_, v_a_4157_);
v___x_4163_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4149_, v___x_4162_, v_a_4123_, v_a_4125_, v_a_4127_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4163_;
}
else
{
lean_dec(v_a_4157_);
lean_dec_ref(v_arg_4152_);
lean_dec_ref(v_arg_4149_);
return v___x_4160_;
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v_arg_4152_);
lean_dec_ref(v_arg_4149_);
v_a_4164_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4156_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4156_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
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
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref(v_e_4122_);
v_a_4173_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4137_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4137_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
v___jp_4134_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_box(0);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object* v_e_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Meta_Grind_propagateBoolAndDown(v_e_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec(v_a_4182_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4195_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4196_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown___boxed), 12, 0);
v___x_4197_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4195_, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8____boxed(lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
return v_res_4199_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_box(0);
v___x_4210_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__2));
v___x_4211_ = l_Lean_mkConst(v___x_4210_, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5(void){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4217_ = lean_box(0);
v___x_4218_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__4));
v___x_4219_ = l_Lean_mkConst(v___x_4218_, v___x_4217_);
return v___x_4219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7(void){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = lean_box(0);
v___x_4226_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__6));
v___x_4227_ = l_Lean_mkConst(v___x_4226_, v___x_4225_);
return v___x_4227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9(void){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4233_ = lean_box(0);
v___x_4234_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__8));
v___x_4235_ = l_Lean_mkConst(v___x_4234_, v___x_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* v_e_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4251_; uint8_t v___x_4252_; 
lean_inc_ref(v_e_4236_);
v___x_4251_ = l_Lean_Expr_cleanupAnnotations(v_e_4236_);
v___x_4252_ = l_Lean_Expr_isApp(v___x_4251_);
if (v___x_4252_ == 0)
{
lean_dec_ref(v___x_4251_);
lean_dec_ref(v_e_4236_);
goto v___jp_4248_;
}
else
{
lean_object* v_arg_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v_arg_4253_ = lean_ctor_get(v___x_4251_, 1);
lean_inc_ref(v_arg_4253_);
v___x_4254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4251_);
v___x_4255_ = l_Lean_Expr_isApp(v___x_4254_);
if (v___x_4255_ == 0)
{
lean_dec_ref(v___x_4254_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
goto v___jp_4248_;
}
else
{
lean_object* v_arg_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v_arg_4256_ = lean_ctor_get(v___x_4254_, 1);
lean_inc_ref(v_arg_4256_);
v___x_4257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4254_);
v___x_4258_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4259_ = l_Lean_Expr_isConstOf(v___x_4257_, v___x_4258_);
lean_dec_ref(v___x_4257_);
if (v___x_4259_ == 0)
{
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
goto v___jp_4248_;
}
else
{
lean_object* v___x_4260_; 
lean_inc_ref(v_arg_4256_);
v___x_4260_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4256_, v_a_4237_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; uint8_t v___x_4262_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
v___x_4262_ = lean_unbox(v_a_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; 
lean_inc_ref(v_arg_4253_);
v___x_4263_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4253_, v_a_4237_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; uint8_t v___x_4265_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
v___x_4265_ = lean_unbox(v_a_4264_);
lean_dec(v_a_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; 
lean_dec(v_a_4261_);
lean_inc_ref(v_arg_4256_);
v___x_4266_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4256_, v_a_4237_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; uint8_t v___x_4268_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v___x_4268_ = lean_unbox(v_a_4267_);
lean_dec(v_a_4267_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_inc_ref(v_arg_4253_);
v___x_4269_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4253_, v_a_4237_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4292_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4292_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4292_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_unbox(v_a_4270_);
lean_dec(v_a_4270_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4277_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v___x_4275_ = lean_box(0);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4275_);
v___x_4277_ = v___x_4272_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
else
{
lean_object* v___x_4279_; 
lean_del_object(v___x_4272_);
lean_inc_ref(v_arg_4253_);
v___x_4279_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4253_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__3, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3);
v___x_4282_ = l_Lean_mkApp3(v___x_4281_, v_arg_4256_, v_arg_4253_, v_a_4280_);
v___x_4283_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4236_, v___x_4282_, v_a_4237_, v_a_4239_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4283_;
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4284_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4279_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4279_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4293_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4269_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4269_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v___x_4301_; 
lean_inc_ref(v_arg_4256_);
v___x_4301_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4256_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__5, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5);
v___x_4304_ = l_Lean_mkApp3(v___x_4303_, v_arg_4256_, v_arg_4253_, v_a_4302_);
v___x_4305_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4236_, v___x_4304_, v_a_4237_, v_a_4239_, v_a_4241_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4305_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4306_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4301_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4301_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
else
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4314_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4266_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4266_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_object* v___x_4322_; 
lean_inc_ref(v_arg_4253_);
v___x_4322_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4253_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4322_, 1);
v___x_4324_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__7, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7);
lean_inc_ref(v_arg_4256_);
v___x_4325_ = l_Lean_mkApp3(v___x_4324_, v_arg_4256_, v_arg_4253_, v_a_4323_);
v___x_4326_ = lean_unbox(v_a_4261_);
lean_dec(v_a_4261_);
v___x_4327_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4236_, v_arg_4256_, v___x_4325_, v___x_4326_, v_a_4237_, v_a_4239_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4327_;
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_a_4261_);
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4328_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4322_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4322_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4261_);
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4336_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4263_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4263_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v___x_4344_; 
lean_dec(v_a_4261_);
lean_inc_ref(v_arg_4256_);
v___x_4344_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4256_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4344_, 1);
v___x_4346_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__9, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9);
lean_inc_ref(v_arg_4253_);
v___x_4347_ = l_Lean_mkApp3(v___x_4346_, v_arg_4256_, v_arg_4253_, v_a_4345_);
v___x_4348_ = 0;
v___x_4349_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4236_, v_arg_4253_, v___x_4347_, v___x_4348_, v_a_4237_, v_a_4239_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4349_;
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4350_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4344_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4344_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec_ref(v_arg_4256_);
lean_dec_ref(v_arg_4253_);
lean_dec_ref(v_e_4236_);
v_a_4358_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4260_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4260_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
}
v___jp_4248_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_box(0);
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
return v___x_4250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object* v_e_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Meta_Grind_propagateBoolOrUp(v_e_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec(v_a_4367_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4380_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4381_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp___boxed), 12, 0);
v___x_4382_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4380_, v___x_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8____boxed(lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
return v_res_4384_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_box(0);
v___x_4391_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__0));
v___x_4392_ = l_Lean_mkConst(v___x_4391_, v___x_4390_);
return v___x_4392_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_box(0);
v___x_4399_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__2));
v___x_4400_ = l_Lean_mkConst(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* v_e_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v___x_4416_; 
lean_inc_ref(v_e_4401_);
v___x_4416_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4401_, v_a_4402_, v_a_4406_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4451_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4419_ = v___x_4416_;
v_isShared_4420_ = v_isSharedCheck_4451_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4416_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4451_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
uint8_t v___x_4421_; 
v___x_4421_ = lean_unbox(v_a_4417_);
lean_dec(v_a_4417_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4424_; 
lean_dec_ref(v_e_4401_);
v___x_4422_ = lean_box(0);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4422_);
v___x_4424_ = v___x_4419_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
else
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
lean_del_object(v___x_4419_);
lean_inc_ref(v_e_4401_);
v___x_4426_ = l_Lean_Expr_cleanupAnnotations(v_e_4401_);
v___x_4427_ = l_Lean_Expr_isApp(v___x_4426_);
if (v___x_4427_ == 0)
{
lean_dec_ref(v___x_4426_);
lean_dec_ref(v_e_4401_);
goto v___jp_4413_;
}
else
{
lean_object* v_arg_4428_; lean_object* v___x_4429_; uint8_t v___x_4430_; 
v_arg_4428_ = lean_ctor_get(v___x_4426_, 1);
lean_inc_ref(v_arg_4428_);
v___x_4429_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4426_);
v___x_4430_ = l_Lean_Expr_isApp(v___x_4429_);
if (v___x_4430_ == 0)
{
lean_dec_ref(v___x_4429_);
lean_dec_ref(v_arg_4428_);
lean_dec_ref(v_e_4401_);
goto v___jp_4413_;
}
else
{
lean_object* v_arg_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; uint8_t v___x_4434_; 
v_arg_4431_ = lean_ctor_get(v___x_4429_, 1);
lean_inc_ref(v_arg_4431_);
v___x_4432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4429_);
v___x_4433_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4434_ = l_Lean_Expr_isConstOf(v___x_4432_, v___x_4433_);
lean_dec_ref(v___x_4432_);
if (v___x_4434_ == 0)
{
lean_dec_ref(v_arg_4431_);
lean_dec_ref(v_arg_4428_);
lean_dec_ref(v_e_4401_);
goto v___jp_4413_;
}
else
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc_n(v_a_4436_, 2);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__1, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1);
lean_inc_ref(v_arg_4428_);
lean_inc_ref_n(v_arg_4431_, 2);
v___x_4438_ = l_Lean_mkApp3(v___x_4437_, v_arg_4431_, v_arg_4428_, v_a_4436_);
v___x_4439_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4431_, v___x_4438_, v_a_4402_, v_a_4404_, v_a_4406_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_dec_ref_known(v___x_4439_, 1);
v___x_4440_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__3, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3);
lean_inc_ref(v_arg_4428_);
v___x_4441_ = l_Lean_mkApp3(v___x_4440_, v_arg_4431_, v_arg_4428_, v_a_4436_);
v___x_4442_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4428_, v___x_4441_, v_a_4402_, v_a_4404_, v_a_4406_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
return v___x_4442_;
}
else
{
lean_dec(v_a_4436_);
lean_dec_ref(v_arg_4431_);
lean_dec_ref(v_arg_4428_);
return v___x_4439_;
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec_ref(v_arg_4431_);
lean_dec_ref(v_arg_4428_);
v_a_4443_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4435_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4435_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
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
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref(v_e_4401_);
v_a_4452_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4416_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4416_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
v___jp_4413_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4414_ = lean_box(0);
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
return v___x_4415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object* v_e_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_Meta_Grind_propagateBoolOrDown(v_e_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec(v_a_4461_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4474_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4475_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown___boxed), 12, 0);
v___x_4476_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4474_, v___x_4475_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8____boxed(lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
return v_res_4478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = lean_box(0);
v___x_4489_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__2));
v___x_4490_ = l_Lean_mkConst(v___x_4489_, v___x_4488_);
return v___x_4490_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_box(0);
v___x_4497_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__4));
v___x_4498_ = l_Lean_mkConst(v___x_4497_, v___x_4496_);
return v___x_4498_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4504_ = lean_box(0);
v___x_4505_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__6));
v___x_4506_ = l_Lean_mkConst(v___x_4505_, v___x_4504_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* v_e_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v___x_4522_; uint8_t v___x_4523_; 
lean_inc_ref(v_e_4507_);
v___x_4522_ = l_Lean_Expr_cleanupAnnotations(v_e_4507_);
v___x_4523_ = l_Lean_Expr_isApp(v___x_4522_);
if (v___x_4523_ == 0)
{
lean_dec_ref(v___x_4522_);
lean_dec_ref(v_e_4507_);
goto v___jp_4519_;
}
else
{
lean_object* v_arg_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v_arg_4524_ = lean_ctor_get(v___x_4522_, 1);
lean_inc_ref(v_arg_4524_);
v___x_4525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4522_);
v___x_4526_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4527_ = l_Lean_Expr_isConstOf(v___x_4525_, v___x_4526_);
lean_dec_ref(v___x_4525_);
if (v___x_4527_ == 0)
{
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
goto v___jp_4519_;
}
else
{
lean_object* v___x_4528_; 
lean_inc_ref(v_arg_4524_);
v___x_4528_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4524_, v_a_4508_, v_a_4512_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; uint8_t v___x_4530_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v___x_4528_, 1);
v___x_4530_ = lean_unbox(v_a_4529_);
lean_dec(v_a_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_inc_ref(v_arg_4524_);
v___x_4531_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4524_, v_a_4508_, v_a_4512_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; uint8_t v___x_4533_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = lean_unbox(v_a_4532_);
lean_dec(v_a_4532_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4507_, v_arg_4524_, v_a_4508_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4557_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4537_ = v___x_4534_;
v_isShared_4538_ = v_isSharedCheck_4557_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4557_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_unbox(v_a_4535_);
lean_dec(v_a_4535_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v___x_4540_ = lean_box(0);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4540_);
v___x_4542_ = v___x_4537_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
else
{
lean_object* v___x_4544_; 
lean_del_object(v___x_4537_);
lean_inc(v_a_4517_);
lean_inc_ref(v_a_4516_);
lean_inc(v_a_4515_);
lean_inc_ref(v_a_4514_);
lean_inc(v_a_4513_);
lean_inc_ref(v_a_4512_);
lean_inc(v_a_4511_);
lean_inc_ref(v_a_4510_);
lean_inc(v_a_4509_);
lean_inc(v_a_4508_);
lean_inc_ref(v_arg_4524_);
v___x_4544_ = lean_grind_mk_eq_proof(v_e_4507_, v_arg_4524_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v___x_4544_, 1);
v___x_4546_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4547_ = l_Lean_mkAppB(v___x_4546_, v_arg_4524_, v_a_4545_);
v___x_4548_ = l_Lean_Meta_Grind_closeGoal(v___x_4547_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
return v___x_4548_;
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec_ref(v_arg_4524_);
v_a_4549_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4544_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4544_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v_a_4558_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4534_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4534_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
else
{
lean_object* v___x_4566_; 
lean_inc_ref(v_arg_4524_);
v___x_4566_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4524_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
v___x_4568_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__5, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5);
v___x_4569_ = l_Lean_mkAppB(v___x_4568_, v_arg_4524_, v_a_4567_);
v___x_4570_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4507_, v___x_4569_, v_a_4508_, v_a_4510_, v_a_4512_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
return v___x_4570_;
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v_a_4571_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4566_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4566_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v_a_4579_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4531_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4531_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
else
{
lean_object* v___x_4587_; 
lean_inc_ref(v_arg_4524_);
v___x_4587_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4524_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v___x_4589_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__7, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7);
v___x_4590_ = l_Lean_mkAppB(v___x_4589_, v_arg_4524_, v_a_4588_);
v___x_4591_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4507_, v___x_4590_, v_a_4508_, v_a_4510_, v_a_4512_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
return v___x_4591_;
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v_a_4592_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4587_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4587_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec_ref(v_arg_4524_);
lean_dec_ref(v_e_4507_);
v_a_4600_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4528_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4528_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
}
v___jp_4519_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = lean_box(0);
v___x_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
return v___x_4521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object* v_e_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_Meta_Grind_propagateBoolNotUp(v_e_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec(v_a_4609_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4623_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp___boxed), 12, 0);
v___x_4624_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4622_, v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8____boxed(lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
return v_res_4626_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4632_ = lean_box(0);
v___x_4633_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__0));
v___x_4634_ = l_Lean_mkConst(v___x_4633_, v___x_4632_);
return v___x_4634_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3(void){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_box(0);
v___x_4641_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__2));
v___x_4642_ = l_Lean_mkConst(v___x_4641_, v___x_4640_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* v_e_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v___x_4658_; uint8_t v___x_4659_; 
lean_inc_ref(v_e_4643_);
v___x_4658_ = l_Lean_Expr_cleanupAnnotations(v_e_4643_);
v___x_4659_ = l_Lean_Expr_isApp(v___x_4658_);
if (v___x_4659_ == 0)
{
lean_dec_ref(v___x_4658_);
lean_dec_ref(v_e_4643_);
goto v___jp_4655_;
}
else
{
lean_object* v_arg_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v_arg_4660_ = lean_ctor_get(v___x_4658_, 1);
lean_inc_ref(v_arg_4660_);
v___x_4661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4658_);
v___x_4662_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4663_ = l_Lean_Expr_isConstOf(v___x_4661_, v___x_4662_);
lean_dec_ref(v___x_4661_);
if (v___x_4663_ == 0)
{
lean_dec_ref(v_arg_4660_);
lean_dec_ref(v_e_4643_);
goto v___jp_4655_;
}
else
{
lean_object* v___x_4664_; 
lean_inc_ref(v_e_4643_);
v___x_4664_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4643_, v_a_4644_, v_a_4648_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; uint8_t v___x_4666_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v___x_4666_ = lean_unbox(v_a_4665_);
lean_dec(v_a_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; 
lean_inc_ref(v_e_4643_);
v___x_4667_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4643_, v_a_4644_, v_a_4648_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; uint8_t v___x_4669_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = lean_unbox(v_a_4668_);
lean_dec(v_a_4668_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4643_, v_arg_4660_, v_a_4644_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4693_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4693_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4693_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
uint8_t v___x_4675_; 
v___x_4675_ = lean_unbox(v_a_4671_);
lean_dec(v_a_4671_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; lean_object* v___x_4678_; 
lean_dec_ref(v_arg_4660_);
lean_dec_ref(v_e_4643_);
v___x_4676_ = lean_box(0);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4676_);
v___x_4678_ = v___x_4673_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
else
{
lean_object* v___x_4680_; 
lean_del_object(v___x_4673_);
lean_inc(v_a_4653_);
lean_inc_ref(v_a_4652_);
lean_inc(v_a_4651_);
lean_inc_ref(v_a_4650_);
lean_inc(v_a_4649_);
lean_inc_ref(v_a_4648_);
lean_inc(v_a_4647_);
lean_inc_ref(v_a_4646_);
lean_inc(v_a_4645_);
lean_inc(v_a_4644_);
lean_inc_ref(v_arg_4660_);
v___x_4680_ = lean_grind_mk_eq_proof(v_e_4643_, v_arg_4660_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
v___x_4682_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4683_ = l_Lean_mkAppB(v___x_4682_, v_arg_4660_, v_a_4681_);
v___x_4684_ = l_Lean_Meta_Grind_closeGoal(v___x_4683_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
return v___x_4684_;
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_dec_ref(v_arg_4660_);
v_a_4685_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4680_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4680_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v_arg_4660_);
lean_dec_ref(v_e_4643_);
v_a_4694_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4670_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4670_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4702_, 1);
v___x_4704_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__1, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1);
lean_inc_ref(v_arg_4660_);
v___x_4705_ = l_Lean_mkAppB(v___x_4704_, v_arg_4660_, v_a_4703_);
v___x_4706_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4660_, v___x_4705_, v_a_4644_, v_a_4646_, v_a_4648_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
return v___x_4706_;
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
lean_dec_ref(v_arg_4660_);
v_a_4707_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___x_4702_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___x_4702_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec_ref(v_arg_4660_);
lean_dec_ref(v_e_4643_);
v_a_4715_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4667_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4667_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
else
{
lean_object* v___x_4723_; 
v___x_4723_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__3, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3);
lean_inc_ref(v_arg_4660_);
v___x_4726_ = l_Lean_mkAppB(v___x_4725_, v_arg_4660_, v_a_4724_);
v___x_4727_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4660_, v___x_4726_, v_a_4644_, v_a_4646_, v_a_4648_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
return v___x_4727_;
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec_ref(v_arg_4660_);
v_a_4728_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4723_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4723_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_dec_ref(v_arg_4660_);
lean_dec_ref(v_e_4643_);
v_a_4736_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4664_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4664_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
}
v___jp_4655_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object* v_e_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Lean_Meta_Grind_propagateBoolNotDown(v_e_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
lean_dec(v_a_4746_);
lean_dec(v_a_4745_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4758_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4759_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown___boxed), 12, 0);
v___x_4760_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4758_, v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8____boxed(lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
return v_res_4762_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
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
