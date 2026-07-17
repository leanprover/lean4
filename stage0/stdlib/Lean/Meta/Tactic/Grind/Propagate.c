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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
uint8_t v_a_143264__boxed_1119_; uint8_t v___x_143265__boxed_1120_; lean_object* v_res_1121_; 
v_a_143264__boxed_1119_ = lean_unbox(v_a_1105_);
v___x_143265__boxed_1120_ = lean_unbox(v___x_1106_);
v_res_1121_ = l_Lean_Meta_Grind_propagateEqUp___lam__0(v_arg_1101_, v_self_1102_, v_arg_1103_, v_self_1104_, v_a_143264__boxed_1119_, v___x_143265__boxed_1120_, v_hab_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
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
uint8_t v_a_143585__boxed_1332_; uint8_t v___x_143586__boxed_1333_; lean_object* v_res_1334_; 
v_a_143585__boxed_1332_ = lean_unbox(v_a_1318_);
v___x_143586__boxed_1333_ = lean_unbox(v___x_1319_);
v_res_1334_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(v_a_1314_, v_self_1315_, v_a_1316_, v_self_1317_, v_a_143585__boxed_1332_, v___x_143586__boxed_1333_, v_hab_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
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
lean_object* v___x_1362_; lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1450_; 
v___x_1362_ = lean_st_ref_get(v___y_1351_);
v_snd_1363_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_a_1350_, 0);
lean_dec(v_unused_1451_);
v___x_1365_ = v_a_1350_;
v_isShared_1366_ = v_isSharedCheck_1450_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_a_1350_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1450_;
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
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1441_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1441_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1441_;
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
lean_object* v_self_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_self_1416_ = lean_ctor_get(v_a_1345_, 0);
v___x_1417_ = l_Lean_Expr_getAppFn(v_self_1416_);
v___x_1418_ = l_Lean_Expr_getAppFn(v_self_1402_);
v___x_1419_ = lean_expr_eqv(v___x_1417_, v___x_1418_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v___x_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_inc_ref(v_self_1402_);
lean_inc_ref(v_self_1416_);
v___x_1420_ = l_Lean_Meta_Grind_hasSameType(v_self_1416_, v_self_1402_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; uint8_t v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = lean_unbox(v_a_1421_);
lean_dec(v_a_1421_);
if (v___x_1422_ == 0)
{
lean_dec_ref(v_self_1402_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
else
{
lean_object* v___x_1423_; 
lean_inc_ref(v_self_1416_);
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_dec_ref(v_a_1345_);
lean_inc_ref(v_a_1344_);
lean_inc_ref(v_a_1349_);
v___x_1423_ = l_Lean_Meta_mkEq(v_a_1349_, v_a_1344_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_box(v_a_1348_);
v___x_1426_ = lean_box(v___x_1347_);
v___f_1427_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1427_, 0, v_a_1349_);
lean_closure_set(v___f_1427_, 1, v_self_1416_);
lean_closure_set(v___f_1427_, 2, v_a_1344_);
lean_closure_set(v___f_1427_, 3, v_self_1402_);
lean_closure_set(v___f_1427_, 4, v___x_1425_);
lean_closure_set(v___f_1427_, 5, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1429_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1428_, v_a_1424_, v___f_1427_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1376_ = v___x_1429_;
goto v___jp_1375_;
}
else
{
lean_dec_ref(v_self_1416_);
lean_dec_ref(v_self_1402_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_a_1344_);
v___y_1376_ = v___x_1423_;
goto v___jp_1375_;
}
}
}
else
{
lean_dec_ref(v_self_1402_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1431_ = lean_unbox(v_a_1430_);
if (v___x_1431_ == 0)
{
lean_dec(v_a_1430_);
lean_del_object(v___x_1365_);
goto v___jp_1406_;
}
else
{
uint8_t v___x_1432_; 
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v___x_1432_ = lean_unbox(v_a_1430_);
lean_dec(v_a_1430_);
v_a_1368_ = v___x_1432_;
goto v___jp_1367_;
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_next_1403_);
lean_del_object(v___x_1400_);
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v_a_1433_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1420_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1420_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
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
size_t v___x_1407_; size_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_ptr_addr(v_next_1403_);
v___x_1408_ = lean_ptr_addr(v_a_1344_);
v___x_1409_ = lean_usize_dec_eq(v___x_1407_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_del_object(v___x_1400_);
lean_dec(v_snd_1363_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1405_);
lean_ctor_set(v___x_1410_, 1, v_next_1403_);
v_a_1350_ = v___x_1410_;
goto _start;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec_ref(v_next_1403_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1405_);
lean_ctor_set(v___x_1412_, 1, v_snd_1363_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1412_);
v___x_1414_ = v___x_1400_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec_ref(v_a_1349_);
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_a_1344_);
v_a_1442_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1397_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1397_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
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
lean_object* v_a_1452_ = _args[0];
lean_object* v_a_1453_ = _args[1];
lean_object* v_e_1454_ = _args[2];
lean_object* v___x_1455_ = _args[3];
lean_object* v_a_1456_ = _args[4];
lean_object* v_a_1457_ = _args[5];
lean_object* v_a_1458_ = _args[6];
lean_object* v___y_1459_ = _args[7];
lean_object* v___y_1460_ = _args[8];
lean_object* v___y_1461_ = _args[9];
lean_object* v___y_1462_ = _args[10];
lean_object* v___y_1463_ = _args[11];
lean_object* v___y_1464_ = _args[12];
lean_object* v___y_1465_ = _args[13];
lean_object* v___y_1466_ = _args[14];
lean_object* v___y_1467_ = _args[15];
lean_object* v___y_1468_ = _args[16];
lean_object* v___y_1469_ = _args[17];
_start:
{
uint8_t v___x_143796__boxed_1470_; uint8_t v_a_143797__boxed_1471_; lean_object* v_res_1472_; 
v___x_143796__boxed_1470_ = lean_unbox(v___x_1455_);
v_a_143797__boxed_1471_ = lean_unbox(v_a_1456_);
v_res_1472_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1452_, v_a_1453_, v_e_1454_, v___x_143796__boxed_1470_, v_a_143797__boxed_1471_, v_a_1457_, v_a_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object* v_a_1473_, lean_object* v_a_1474_, uint8_t v_a_1475_, uint8_t v___x_1476_, lean_object* v_a_1477_, lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1579_; 
v___x_1491_ = lean_st_ref_get(v___y_1480_);
v_snd_1492_ = lean_ctor_get(v_a_1479_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1479_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_a_1479_, 0);
lean_dec(v_unused_1580_);
v___x_1494_ = v_a_1479_;
v_isShared_1495_ = v_isSharedCheck_1579_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_a_1479_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1579_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v_a_1497_; lean_object* v___y_1505_; lean_object* v___x_1526_; 
lean_inc(v_snd_1492_);
v___x_1526_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1491_, v_snd_1492_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___x_1491_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1570_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1529_ = v___x_1526_;
v_isShared_1530_ = v_isSharedCheck_1570_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1570_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_self_1531_; lean_object* v_next_1532_; uint8_t v_ctor_1533_; lean_object* v___x_1534_; 
v_self_1531_ = lean_ctor_get(v_a_1527_, 0);
lean_inc_ref(v_self_1531_);
v_next_1532_ = lean_ctor_get(v_a_1527_, 1);
lean_inc_ref(v_next_1532_);
v_ctor_1533_ = lean_ctor_get_uint8(v_a_1527_, sizeof(void*)*12 + 2);
lean_dec(v_a_1527_);
v___x_1534_ = lean_box(0);
if (v_ctor_1533_ == 0)
{
lean_dec_ref(v_self_1531_);
lean_del_object(v___x_1494_);
goto v___jp_1535_;
}
else
{
lean_object* v_self_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_self_1545_ = lean_ctor_get(v_a_1474_, 0);
v___x_1546_ = l_Lean_Expr_getAppFn(v_self_1545_);
v___x_1547_ = l_Lean_Expr_getAppFn(v_self_1531_);
v___x_1548_ = lean_expr_eqv(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1547_);
lean_dec_ref(v___x_1546_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_inc_ref(v_self_1531_);
lean_inc_ref(v_self_1545_);
v___x_1549_ = l_Lean_Meta_Grind_hasSameType(v_self_1545_, v_self_1531_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; uint8_t v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = lean_unbox(v_a_1550_);
lean_dec(v_a_1550_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v_self_1531_);
lean_del_object(v___x_1494_);
goto v___jp_1535_;
}
else
{
lean_object* v___x_1552_; 
lean_inc_ref(v_self_1545_);
lean_dec_ref(v_next_1532_);
lean_del_object(v___x_1529_);
lean_dec_ref(v_a_1474_);
lean_inc_ref(v_a_1473_);
lean_inc_ref(v_a_1477_);
v___x_1552_ = l_Lean_Meta_mkEq(v_a_1477_, v_a_1473_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = lean_box(v_a_1475_);
v___x_1555_ = lean_box(v___x_1476_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1556_, 0, v_a_1477_);
lean_closure_set(v___f_1556_, 1, v_self_1545_);
lean_closure_set(v___f_1556_, 2, v_a_1473_);
lean_closure_set(v___f_1556_, 3, v_self_1531_);
lean_closure_set(v___f_1556_, 4, v___x_1554_);
lean_closure_set(v___f_1556_, 5, v___x_1555_);
v___x_1557_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1558_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1557_, v_a_1553_, v___f_1556_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v___y_1505_ = v___x_1558_;
goto v___jp_1504_;
}
else
{
lean_dec_ref(v_self_1545_);
lean_dec_ref(v_self_1531_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_a_1473_);
v___y_1505_ = v___x_1552_;
goto v___jp_1504_;
}
}
}
else
{
lean_dec_ref(v_self_1531_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1559_; uint8_t v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1560_ = lean_unbox(v_a_1559_);
if (v___x_1560_ == 0)
{
lean_dec(v_a_1559_);
lean_del_object(v___x_1494_);
goto v___jp_1535_;
}
else
{
uint8_t v___x_1561_; 
lean_dec_ref(v_next_1532_);
lean_del_object(v___x_1529_);
lean_dec_ref(v_e_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_a_1474_);
lean_dec_ref(v_a_1473_);
v___x_1561_ = lean_unbox(v_a_1559_);
lean_dec(v_a_1559_);
v_a_1497_ = v___x_1561_;
goto v___jp_1496_;
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_next_1532_);
lean_del_object(v___x_1529_);
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_e_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_a_1474_);
lean_dec_ref(v_a_1473_);
v_a_1562_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1549_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1549_);
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
}
else
{
lean_dec_ref(v_self_1531_);
lean_del_object(v___x_1494_);
goto v___jp_1535_;
}
}
v___jp_1535_:
{
size_t v___x_1536_; size_t v___x_1537_; uint8_t v___x_1538_; 
v___x_1536_ = lean_ptr_addr(v_next_1532_);
v___x_1537_ = lean_ptr_addr(v_a_1473_);
v___x_1538_ = lean_usize_dec_eq(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_del_object(v___x_1529_);
lean_dec(v_snd_1492_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1534_);
lean_ctor_set(v___x_1539_, 1, v_next_1532_);
v___x_1540_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1473_, v_a_1474_, v_e_1478_, v___x_1476_, v_a_1475_, v_a_1477_, v___x_1539_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec_ref(v_next_1532_);
lean_dec_ref(v_e_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_a_1474_);
lean_dec_ref(v_a_1473_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1534_);
lean_ctor_set(v___x_1541_, 1, v_snd_1492_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1541_);
v___x_1543_ = v___x_1529_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
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
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_e_1478_);
lean_dec_ref(v_a_1477_);
lean_dec_ref(v_a_1474_);
lean_dec_ref(v_a_1473_);
v_a_1571_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1526_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1526_);
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
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1498_ = lean_box(v_a_1497_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1499_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1492_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
return v___x_1502_;
}
}
v___jp_1504_:
{
if (lean_obj_tag(v___y_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1506_ = lean_ctor_get(v___y_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___y_1505_, 1);
v___x_1507_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1478_);
v___x_1508_ = l_Lean_mkAppB(v___x_1507_, v_e_1478_, v_a_1506_);
v___x_1509_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1478_, v___x_1508_, v___y_1480_, v___y_1482_, v___y_1484_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
v_a_1497_ = v___x_1476_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_e_1478_);
v_a_1518_ = lean_ctor_get(v___y_1505_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___y_1505_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___y_1505_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___y_1505_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
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
uint8_t v_a_144034__boxed_1599_; uint8_t v___x_144035__boxed_1600_; lean_object* v_res_1601_; 
v_a_144034__boxed_1599_ = lean_unbox(v_a_1583_);
v___x_144035__boxed_1600_ = lean_unbox(v___x_1584_);
v_res_1601_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1581_, v_a_1582_, v_a_144034__boxed_1599_, v___x_144035__boxed_1600_, v_a_1585_, v_e_1586_, v_a_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
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
lean_object* v___x_1619_; lean_object* v_snd_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1676_; 
v___x_1619_ = lean_st_ref_get(v___y_1608_);
v_snd_1620_ = lean_ctor_get(v_a_1607_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_a_1607_, 0);
lean_dec(v_unused_1677_);
v___x_1622_ = v_a_1607_;
v_isShared_1623_ = v_isSharedCheck_1676_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snd_1620_);
lean_dec(v_a_1607_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1676_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
lean_inc(v_snd_1620_);
v___x_1624_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1619_, v_snd_1620_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___x_1619_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1667_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1667_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1667_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_next_1629_; uint8_t v_ctor_1630_; lean_object* v___x_1631_; 
v_next_1629_ = lean_ctor_get(v_a_1625_, 1);
lean_inc_ref(v_next_1629_);
v_ctor_1630_ = lean_ctor_get_uint8(v_a_1625_, sizeof(void*)*12 + 2);
v___x_1631_ = lean_box(0);
if (v_ctor_1630_ == 0)
{
lean_dec(v_a_1625_);
goto v___jp_1632_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_inc_ref_n(v_a_1603_, 2);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1631_);
lean_ctor_set(v___x_1646_, 1, v_a_1603_);
lean_inc_ref(v_e_1606_);
lean_inc_ref(v_a_1602_);
v___x_1647_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1603_, v_a_1625_, v_a_1604_, v___x_1605_, v_a_1602_, v_e_1606_, v___x_1646_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
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
lean_dec_ref(v_next_1629_);
lean_del_object(v___x_1627_);
lean_del_object(v___x_1622_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_snd_1620_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_fst_1652_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_snd_1620_);
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
lean_dec_ref(v_next_1629_);
lean_del_object(v___x_1627_);
lean_del_object(v___x_1622_);
lean_dec(v_snd_1620_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v___x_1647_;
}
}
v___jp_1632_:
{
size_t v___x_1633_; size_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_ptr_addr(v_next_1629_);
v___x_1634_ = lean_ptr_addr(v_a_1602_);
v___x_1635_ = lean_usize_dec_eq(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1637_; 
lean_del_object(v___x_1627_);
lean_dec(v_snd_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v_next_1629_);
lean_ctor_set(v___x_1622_, 0, v___x_1631_);
v___x_1637_ = v___x_1622_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_next_1629_);
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
lean_dec_ref(v_next_1629_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1631_);
v___x_1641_ = v___x_1622_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_snd_1620_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1641_);
v___x_1643_ = v___x_1627_;
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
lean_del_object(v___x_1622_);
lean_dec(v_snd_1620_);
lean_dec_ref(v_e_1606_);
lean_dec_ref(v_a_1603_);
lean_dec_ref(v_a_1602_);
v_a_1668_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1624_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1624_);
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
uint8_t v_a_144258__boxed_1695_; uint8_t v___x_144259__boxed_1696_; lean_object* v_res_1697_; 
v_a_144258__boxed_1695_ = lean_unbox(v_a_1680_);
v___x_144259__boxed_1696_ = lean_unbox(v___x_1681_);
v_res_1697_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_1678_, v_a_1679_, v_a_144258__boxed_1695_, v___x_144259__boxed_1696_, v_e_1682_, v_a_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
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
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__7(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__6));
v___x_1712_ = l_Lean_mkConst(v___x_1711_, v___x_1710_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__10(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_box(0);
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__9));
v___x_1720_ = l_Lean_mkConst(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
lean_inc_ref(v_e_1721_);
v___x_1760_ = l_Lean_Expr_cleanupAnnotations(v_e_1721_);
v___x_1761_ = l_Lean_Expr_isApp(v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec_ref(v___x_1760_);
lean_dec_ref(v_e_1721_);
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_arg_1762_ = lean_ctor_get(v___x_1760_, 1);
lean_inc_ref(v_arg_1762_);
v___x_1763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1760_);
v___x_1764_ = l_Lean_Expr_isApp(v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v___x_1763_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1765_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; uint8_t v___y_1778_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_arg_1765_ = lean_ctor_get(v___x_1763_, 1);
lean_inc_ref(v_arg_1765_);
v___x_1809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1763_);
v___x_1810_ = l_Lean_Expr_isApp(v___x_1809_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1733_;
}
else
{
lean_object* v_arg_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_arg_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc_ref(v_arg_1811_);
v___x_1812_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1809_);
v___x_1813_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_1814_ = l_Lean_Expr_isConstOf(v___x_1812_, v___x_1813_);
lean_dec_ref(v___x_1812_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1815_; 
lean_inc_ref(v_arg_1765_);
v___x_1815_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1765_, v_a_1722_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
lean_inc_ref(v_arg_1762_);
v___x_1817_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1762_, v_a_1722_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1819_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1726_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v_self_1821_; uint8_t v_ctor_1822_; lean_object* v_self_1823_; uint8_t v_ctor_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; size_t v___x_1986_; size_t v___x_1987_; uint8_t v___x_1988_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v_self_1821_ = lean_ctor_get(v_a_1816_, 0);
lean_inc_ref(v_self_1821_);
v_ctor_1822_ = lean_ctor_get_uint8(v_a_1816_, sizeof(void*)*12 + 2);
lean_dec(v_a_1816_);
v_self_1823_ = lean_ctor_get(v_a_1818_, 0);
lean_inc_ref(v_self_1823_);
v_ctor_1824_ = lean_ctor_get_uint8(v_a_1818_, sizeof(void*)*12 + 2);
lean_dec(v_a_1818_);
v___x_1986_ = lean_ptr_addr(v_self_1821_);
v___x_1987_ = lean_ptr_addr(v_a_1820_);
v___x_1988_ = lean_usize_dec_eq(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
size_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_ptr_addr(v_self_1823_);
v___x_1990_ = lean_usize_dec_eq(v___x_1989_, v___x_1987_);
if (v___x_1990_ == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_usize_dec_eq(v___x_1986_, v___x_1989_);
if (v___x_1991_ == 0)
{
lean_dec(v_a_1820_);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_st_ref_get(v_a_1722_);
lean_inc_ref(v_e_1721_);
v___x_1993_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1992_, v_e_1721_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v___x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = lean_ptr_addr(v_a_1994_);
lean_dec(v_a_1994_);
v___x_1996_ = lean_usize_dec_eq(v___x_1995_, v___x_1987_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
lean_inc(v_a_1727_);
lean_inc_ref(v_a_1726_);
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_inc_ref(v_arg_1762_);
lean_inc_ref(v_arg_1765_);
v___x_1997_ = lean_grind_mk_eq_proof(v_arg_1765_, v_arg_1762_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
lean_inc_ref_n(v_e_1721_, 2);
v___x_1999_ = l_Lean_Meta_mkEqTrueCore(v_e_1721_, v_a_1998_);
v___x_2000_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1721_, v_a_1820_, v___x_1999_, v___x_1996_, v_a_1722_, v_a_1724_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref_known(v___x_2000_, 1);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
else
{
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
return v___x_2000_;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2001_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1997_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1997_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_dec(v_a_1820_);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2009_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1993_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1993_);
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
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_st_ref_get(v_a_1722_);
lean_inc_ref(v_e_1721_);
v___x_2018_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2017_, v_e_1721_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; size_t v___x_2020_; uint8_t v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = lean_ptr_addr(v_a_2019_);
lean_dec(v_a_2019_);
v___x_2021_ = lean_usize_dec_eq(v___x_2020_, v___x_1986_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
lean_inc(v_a_1727_);
lean_inc_ref(v_a_1726_);
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_inc_ref(v_arg_1762_);
v___x_2022_ = lean_grind_mk_eq_proof(v_arg_1762_, v_a_1820_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__7, &l_Lean_Meta_Grind_propagateEqUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__7);
lean_inc_ref(v_arg_1762_);
lean_inc_ref_n(v_arg_1765_, 2);
v___x_2025_ = l_Lean_mkApp3(v___x_2024_, v_arg_1765_, v_arg_1762_, v_a_2023_);
lean_inc_ref(v_e_1721_);
v___x_2026_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1721_, v_arg_1765_, v___x_2025_, v___x_2021_, v_a_1722_, v_a_1724_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref_known(v___x_2026_, 1);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
else
{
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
return v___x_2026_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2027_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2022_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_dec(v_a_1820_);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2035_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2018_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2018_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_st_ref_get(v_a_1722_);
lean_inc_ref(v_e_1721_);
v___x_2044_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2043_, v_e_1721_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v___x_2043_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; size_t v___x_2046_; size_t v___x_2047_; uint8_t v___x_2048_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = lean_ptr_addr(v_a_2045_);
lean_dec(v_a_2045_);
v___x_2047_ = lean_ptr_addr(v_self_1823_);
v___x_2048_ = lean_usize_dec_eq(v___x_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_inc(v_a_1731_);
lean_inc_ref(v_a_1730_);
lean_inc(v_a_1729_);
lean_inc_ref(v_a_1728_);
lean_inc(v_a_1727_);
lean_inc_ref(v_a_1726_);
lean_inc(v_a_1725_);
lean_inc_ref(v_a_1724_);
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_inc_ref(v_arg_1765_);
v___x_2049_ = lean_grind_mk_eq_proof(v_arg_1765_, v_a_1820_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__10, &l_Lean_Meta_Grind_propagateEqUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__10);
lean_inc_ref_n(v_arg_1762_, 2);
lean_inc_ref(v_arg_1765_);
v___x_2052_ = l_Lean_mkApp3(v___x_2051_, v_arg_1765_, v_arg_1762_, v_a_2050_);
lean_inc_ref(v_e_1721_);
v___x_2053_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1721_, v_arg_1762_, v___x_2052_, v___x_2048_, v_a_1722_, v_a_1724_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref_known(v___x_2053_, 1);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
else
{
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
return v___x_2053_;
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2054_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2049_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2049_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_dec(v_a_1820_);
v___y_1875_ = v_a_1722_;
v___y_1876_ = v_a_1723_;
v___y_1877_ = v_a_1724_;
v___y_1878_ = v_a_1725_;
v___y_1879_ = v_a_1726_;
v___y_1880_ = v_a_1727_;
v___y_1881_ = v_a_1728_;
v___y_1882_ = v_a_1729_;
v___y_1883_ = v_a_1730_;
v___y_1884_ = v_a_1731_;
goto v___jp_1874_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2062_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2044_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2044_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
v___jp_1825_:
{
if (v___y_1839_ == 0)
{
size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_ptr_addr(v_self_1821_);
lean_dec_ref(v_self_1821_);
v___x_1841_ = lean_ptr_addr(v___y_1838_);
lean_dec_ref(v___y_1838_);
v___x_1842_ = lean_usize_dec_eq(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_self_1823_);
v___y_1767_ = v___y_1826_;
v___y_1768_ = v___y_1833_;
v___y_1769_ = v___y_1834_;
v___y_1770_ = v___y_1835_;
v___y_1771_ = v___y_1836_;
v___y_1772_ = v___y_1837_;
v___y_1773_ = v___y_1828_;
v___y_1774_ = v___y_1829_;
v___y_1775_ = v___y_1830_;
v___y_1776_ = v___y_1831_;
v___y_1777_ = v___y_1832_;
v___y_1778_ = v___x_1842_;
goto v___jp_1766_;
}
else
{
size_t v___x_1843_; size_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1843_ = lean_ptr_addr(v_self_1823_);
lean_dec_ref(v_self_1823_);
v___x_1844_ = lean_ptr_addr(v___y_1827_);
lean_dec_ref(v___y_1827_);
v___x_1845_ = lean_usize_dec_eq(v___x_1843_, v___x_1844_);
v___y_1767_ = v___y_1826_;
v___y_1768_ = v___y_1833_;
v___y_1769_ = v___y_1834_;
v___y_1770_ = v___y_1835_;
v___y_1771_ = v___y_1836_;
v___y_1772_ = v___y_1837_;
v___y_1773_ = v___y_1828_;
v___y_1774_ = v___y_1829_;
v___y_1775_ = v___y_1830_;
v___y_1776_ = v___y_1831_;
v___y_1777_ = v___y_1832_;
v___y_1778_ = v___x_1845_;
goto v___jp_1766_;
}
}
else
{
lean_object* v___x_1846_; 
lean_dec_ref(v___y_1838_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_inc_ref(v_arg_1765_);
v___x_1846_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1765_, v___y_1831_, v___y_1833_, v___y_1836_, v___y_1830_, v___y_1834_, v___y_1832_, v___y_1826_, v___y_1835_, v___y_1829_, v___y_1828_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
lean_inc_ref(v_arg_1762_);
v___x_1848_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1762_, v___y_1831_, v___y_1833_, v___y_1836_, v___y_1830_, v___y_1834_, v___y_1832_, v___y_1826_, v___y_1835_, v___y_1829_, v___y_1828_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1851_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1852_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
lean_inc_ref(v___y_1837_);
v___x_1853_ = l_Lean_Name_mkStr4(v___x_1850_, v___x_1851_, v___y_1837_, v___x_1852_);
v___x_1854_ = lean_box(0);
v___x_1855_ = l_Lean_mkConst(v___x_1853_, v___x_1854_);
v___x_1856_ = l_Lean_mkApp4(v___x_1855_, v_arg_1765_, v_arg_1762_, v_a_1847_, v_a_1849_);
v___x_1857_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1721_, v___x_1856_, v___y_1831_, v___y_1836_, v___y_1834_, v___y_1826_, v___y_1835_, v___y_1829_, v___y_1828_);
return v___x_1857_;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1847_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1858_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1848_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1848_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1866_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1846_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1846_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
v___jp_1874_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__0));
v___x_1886_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
v___x_1887_ = l_Lean_Expr_isConstOf(v_arg_1811_, v___x_1886_);
lean_dec_ref(v_arg_1811_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_inc_ref(v_e_1721_);
v___x_1888_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1721_, v___y_1875_, v___y_1879_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1939_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1939_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1939_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_unbox(v_a_1889_);
if (v___x_1893_ == 0)
{
lean_del_object(v___x_1891_);
if (v_ctor_1822_ == 0)
{
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1757_;
}
else
{
if (v_ctor_1824_ == 0)
{
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1894_ = l_Lean_Expr_getAppFn(v_self_1821_);
v___x_1895_ = l_Lean_Expr_getAppFn(v_self_1823_);
v___x_1896_ = lean_expr_eqv(v___x_1894_, v___x_1895_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v___x_1894_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_inc_ref(v_self_1823_);
lean_inc_ref(v_self_1821_);
v___x_1897_ = l_Lean_Meta_Grind_hasSameType(v_self_1821_, v_self_1823_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
v___x_1900_ = lean_box(0);
lean_inc_ref(v_arg_1765_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_arg_1765_);
v___x_1902_ = lean_unbox(v_a_1889_);
lean_dec(v_a_1889_);
v___x_1903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_arg_1765_, v_arg_1762_, v___x_1902_, v___x_1814_, v_e_1721_, v___x_1901_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1903_, 0);
lean_dec(v_unused_1912_);
v___x_1905_ = v___x_1903_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v___x_1903_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1903_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1903_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v___x_1921_; 
lean_inc_ref(v_arg_1762_);
lean_inc_ref(v_arg_1765_);
v___x_1921_ = l_Lean_Meta_mkEq(v_arg_1765_, v_arg_1762_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = lean_box(v___x_1814_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1924_, 0, v_arg_1765_);
lean_closure_set(v___f_1924_, 1, v_self_1821_);
lean_closure_set(v___f_1924_, 2, v_arg_1762_);
lean_closure_set(v___f_1924_, 3, v_self_1823_);
lean_closure_set(v___f_1924_, 4, v_a_1889_);
lean_closure_set(v___f_1924_, 5, v___x_1923_);
v___x_1925_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1926_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1925_, v_a_1922_, v___f_1924_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
v___y_1737_ = v___y_1881_;
v___y_1738_ = v___y_1879_;
v___y_1739_ = v___y_1882_;
v___y_1740_ = v___y_1877_;
v___y_1741_ = v___y_1884_;
v___y_1742_ = v___y_1883_;
v___y_1743_ = v___y_1875_;
v___y_1744_ = v___x_1926_;
goto v___jp_1736_;
}
else
{
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
v___y_1737_ = v___y_1881_;
v___y_1738_ = v___y_1879_;
v___y_1739_ = v___y_1882_;
v___y_1740_ = v___y_1877_;
v___y_1741_ = v___y_1884_;
v___y_1742_ = v___y_1883_;
v___y_1743_ = v___y_1875_;
v___y_1744_ = v___x_1921_;
goto v___jp_1736_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1927_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1897_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1897_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
goto v___jp_1757_;
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_dec(v_a_1889_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v___x_1935_ = lean_box(0);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1935_);
v___x_1937_ = v___x_1891_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
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
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1940_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1888_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1888_);
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
else
{
lean_object* v___x_1948_; 
lean_inc_ref(v_e_1721_);
v___x_1948_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1721_, v___y_1875_, v___y_1879_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_1879_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_1879_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; size_t v___x_1955_; size_t v___x_1956_; uint8_t v___x_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = lean_ptr_addr(v_self_1821_);
v___x_1956_ = lean_ptr_addr(v_a_1952_);
v___x_1957_ = lean_usize_dec_eq(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1826_ = v___y_1881_;
v___y_1827_ = v_a_1952_;
v___y_1828_ = v___y_1884_;
v___y_1829_ = v___y_1883_;
v___y_1830_ = v___y_1878_;
v___y_1831_ = v___y_1875_;
v___y_1832_ = v___y_1880_;
v___y_1833_ = v___y_1876_;
v___y_1834_ = v___y_1879_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___y_1877_;
v___y_1837_ = v___x_1885_;
v___y_1838_ = v_a_1954_;
v___y_1839_ = v___x_1957_;
goto v___jp_1825_;
}
else
{
size_t v___x_1958_; size_t v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_ptr_addr(v_self_1823_);
v___x_1959_ = lean_ptr_addr(v_a_1954_);
v___x_1960_ = lean_usize_dec_eq(v___x_1958_, v___x_1959_);
v___y_1826_ = v___y_1881_;
v___y_1827_ = v_a_1952_;
v___y_1828_ = v___y_1884_;
v___y_1829_ = v___y_1883_;
v___y_1830_ = v___y_1878_;
v___y_1831_ = v___y_1875_;
v___y_1832_ = v___y_1880_;
v___y_1833_ = v___y_1876_;
v___y_1834_ = v___y_1879_;
v___y_1835_ = v___y_1882_;
v___y_1836_ = v___y_1877_;
v___y_1837_ = v___x_1885_;
v___y_1838_ = v_a_1954_;
v___y_1839_ = v___x_1960_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_a_1952_);
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1961_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1953_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1953_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1969_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1951_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1951_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
v___x_1977_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_1721_, v_arg_1765_, v_arg_1762_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1977_;
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_self_1823_);
lean_dec_ref(v_self_1821_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1978_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1948_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1948_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_a_1818_);
lean_dec(v_a_1816_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2070_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1819_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1819_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_1816_);
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2078_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1817_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1817_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_arg_1811_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_2086_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1815_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1815_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
v___jp_1766_:
{
if (v___y_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; 
lean_inc_ref(v_arg_1765_);
v___x_1781_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1765_, v___y_1776_, v___y_1768_, v___y_1771_, v___y_1775_, v___y_1769_, v___y_1777_, v___y_1767_, v___y_1770_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
lean_inc_ref(v_arg_1762_);
v___x_1783_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1762_, v___y_1776_, v___y_1768_, v___y_1771_, v___y_1775_, v___y_1769_, v___y_1777_, v___y_1767_, v___y_1770_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1786_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1787_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__0));
lean_inc_ref(v___y_1772_);
v___x_1788_ = l_Lean_Name_mkStr4(v___x_1785_, v___x_1786_, v___y_1772_, v___x_1787_);
v___x_1789_ = lean_box(0);
v___x_1790_ = l_Lean_mkConst(v___x_1788_, v___x_1789_);
v___x_1791_ = l_Lean_mkApp4(v___x_1790_, v_arg_1765_, v_arg_1762_, v_a_1782_, v_a_1784_);
v___x_1792_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1721_, v___x_1791_, v___y_1776_, v___y_1771_, v___y_1769_, v___y_1767_, v___y_1770_, v___y_1774_, v___y_1773_);
return v___x_1792_;
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1782_);
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1793_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1783_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1783_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_arg_1765_);
lean_dec_ref(v_arg_1762_);
lean_dec_ref(v_e_1721_);
v_a_1801_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1781_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1781_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
}
v___jp_1733_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
v___jp_1736_:
{
if (lean_obj_tag(v___y_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_a_1745_ = lean_ctor_get(v___y_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___y_1744_, 1);
v___x_1746_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1721_);
v___x_1747_ = l_Lean_mkAppB(v___x_1746_, v_e_1721_, v_a_1745_);
v___x_1748_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1721_, v___x_1747_, v___y_1743_, v___y_1740_, v___y_1738_, v___y_1737_, v___y_1739_, v___y_1742_, v___y_1741_);
return v___x_1748_;
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec_ref(v_e_1721_);
v_a_1749_ = lean_ctor_get(v___y_1744_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___y_1744_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___y_1744_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___y_1744_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object* v_e_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Meta_Grind_propagateEqUp(v_e_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec(v_a_2095_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object* v_00_u03b1_2107_, lean_object* v_name_2108_, uint8_t v_bi_2109_, lean_object* v_type_2110_, lean_object* v_k_2111_, uint8_t v_kind_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_2108_, v_bi_2109_, v_type_2110_, v_k_2111_, v_kind_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_2125_ = _args[0];
lean_object* v_name_2126_ = _args[1];
lean_object* v_bi_2127_ = _args[2];
lean_object* v_type_2128_ = _args[3];
lean_object* v_k_2129_ = _args[4];
lean_object* v_kind_2130_ = _args[5];
lean_object* v___y_2131_ = _args[6];
lean_object* v___y_2132_ = _args[7];
lean_object* v___y_2133_ = _args[8];
lean_object* v___y_2134_ = _args[9];
lean_object* v___y_2135_ = _args[10];
lean_object* v___y_2136_ = _args[11];
lean_object* v___y_2137_ = _args[12];
lean_object* v___y_2138_ = _args[13];
lean_object* v___y_2139_ = _args[14];
lean_object* v___y_2140_ = _args[15];
lean_object* v___y_2141_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2142_; uint8_t v_kind_boxed_2143_; lean_object* v_res_2144_; 
v_bi_boxed_2142_ = lean_unbox(v_bi_2127_);
v_kind_boxed_2143_ = lean_unbox(v_kind_2130_);
v_res_2144_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(v_00_u03b1_2125_, v_name_2126_, v_bi_boxed_2142_, v_type_2128_, v_k_2129_, v_kind_boxed_2143_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec(v___y_2131_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object* v_00_u03b1_2145_, lean_object* v_name_2146_, lean_object* v_type_2147_, lean_object* v_k_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_2146_, v_type_2147_, v_k_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, lean_object* v_type_2163_, lean_object* v_k_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(v_00_u03b1_2161_, v_name_2162_, v_type_2163_, v_k_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object* v_a_2177_, lean_object* v_a_2178_, uint8_t v_a_2179_, uint8_t v___x_2180_, lean_object* v_a_2181_, lean_object* v_e_2182_, lean_object* v_inst_2183_, lean_object* v_a_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_2177_, v_a_2178_, v_a_2179_, v___x_2180_, v_a_2181_, v_e_2182_, v_a_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object** _args){
lean_object* v_a_2197_ = _args[0];
lean_object* v_a_2198_ = _args[1];
lean_object* v_a_2199_ = _args[2];
lean_object* v___x_2200_ = _args[3];
lean_object* v_a_2201_ = _args[4];
lean_object* v_e_2202_ = _args[5];
lean_object* v_inst_2203_ = _args[6];
lean_object* v_a_2204_ = _args[7];
lean_object* v___y_2205_ = _args[8];
lean_object* v___y_2206_ = _args[9];
lean_object* v___y_2207_ = _args[10];
lean_object* v___y_2208_ = _args[11];
lean_object* v___y_2209_ = _args[12];
lean_object* v___y_2210_ = _args[13];
lean_object* v___y_2211_ = _args[14];
lean_object* v___y_2212_ = _args[15];
lean_object* v___y_2213_ = _args[16];
lean_object* v___y_2214_ = _args[17];
lean_object* v___y_2215_ = _args[18];
_start:
{
uint8_t v_a_145299__boxed_2216_; uint8_t v___x_145300__boxed_2217_; lean_object* v_res_2218_; 
v_a_145299__boxed_2216_ = lean_unbox(v_a_2199_);
v___x_145300__boxed_2217_ = lean_unbox(v___x_2200_);
v_res_2218_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(v_a_2197_, v_a_2198_, v_a_145299__boxed_2216_, v___x_145300__boxed_2217_, v_a_2201_, v_e_2202_, v_inst_2203_, v_a_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec(v___y_2205_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object* v_a_2219_, lean_object* v_a_2220_, uint8_t v_a_2221_, uint8_t v___x_2222_, lean_object* v_e_2223_, lean_object* v_inst_2224_, lean_object* v_a_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_2219_, v_a_2220_, v_a_2221_, v___x_2222_, v_e_2223_, v_a_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object** _args){
lean_object* v_a_2238_ = _args[0];
lean_object* v_a_2239_ = _args[1];
lean_object* v_a_2240_ = _args[2];
lean_object* v___x_2241_ = _args[3];
lean_object* v_e_2242_ = _args[4];
lean_object* v_inst_2243_ = _args[5];
lean_object* v_a_2244_ = _args[6];
lean_object* v___y_2245_ = _args[7];
lean_object* v___y_2246_ = _args[8];
lean_object* v___y_2247_ = _args[9];
lean_object* v___y_2248_ = _args[10];
lean_object* v___y_2249_ = _args[11];
lean_object* v___y_2250_ = _args[12];
lean_object* v___y_2251_ = _args[13];
lean_object* v___y_2252_ = _args[14];
lean_object* v___y_2253_ = _args[15];
lean_object* v___y_2254_ = _args[16];
lean_object* v___y_2255_ = _args[17];
_start:
{
uint8_t v_a_145352__boxed_2256_; uint8_t v___x_145353__boxed_2257_; lean_object* v_res_2258_; 
v_a_145352__boxed_2256_ = lean_unbox(v_a_2240_);
v___x_145353__boxed_2257_ = lean_unbox(v___x_2241_);
v_res_2258_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(v_a_2238_, v_a_2239_, v_a_145352__boxed_2256_, v___x_145353__boxed_2257_, v_e_2242_, v_inst_2243_, v_a_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec(v___y_2245_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_e_2261_, uint8_t v___x_2262_, uint8_t v_a_2263_, lean_object* v_a_2264_, lean_object* v_inst_2265_, lean_object* v_a_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_2259_, v_a_2260_, v_e_2261_, v___x_2262_, v_a_2263_, v_a_2264_, v_a_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_a_2279_ = _args[0];
lean_object* v_a_2280_ = _args[1];
lean_object* v_e_2281_ = _args[2];
lean_object* v___x_2282_ = _args[3];
lean_object* v_a_2283_ = _args[4];
lean_object* v_a_2284_ = _args[5];
lean_object* v_inst_2285_ = _args[6];
lean_object* v_a_2286_ = _args[7];
lean_object* v___y_2287_ = _args[8];
lean_object* v___y_2288_ = _args[9];
lean_object* v___y_2289_ = _args[10];
lean_object* v___y_2290_ = _args[11];
lean_object* v___y_2291_ = _args[12];
lean_object* v___y_2292_ = _args[13];
lean_object* v___y_2293_ = _args[14];
lean_object* v___y_2294_ = _args[15];
lean_object* v___y_2295_ = _args[16];
lean_object* v___y_2296_ = _args[17];
lean_object* v___y_2297_ = _args[18];
_start:
{
uint8_t v___x_145402__boxed_2298_; uint8_t v_a_145403__boxed_2299_; lean_object* v_res_2300_; 
v___x_145402__boxed_2298_ = lean_unbox(v___x_2282_);
v_a_145403__boxed_2299_ = lean_unbox(v_a_2283_);
v_res_2300_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(v_a_2279_, v_a_2280_, v_e_2281_, v___x_145402__boxed_2298_, v_a_145403__boxed_2299_, v_a_2284_, v_inst_2285_, v_a_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2303_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___boxed), 12, 0);
v___x_2304_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2302_, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8____boxed(lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_8_();
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* v_e_2307_, lean_object* v_as_2308_, size_t v_sz_2309_, size_t v_i_2310_, lean_object* v_b_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = lean_usize_dec_lt(v_i_2310_, v_sz_2309_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
lean_dec_ref(v_e_2307_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_b_2311_);
return v___x_2324_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_array_uget_borrowed(v_as_2308_, v_i_2310_);
lean_inc_ref(v_e_2307_);
lean_inc(v_a_2325_);
v___x_2326_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_a_2325_, v_e_2307_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; 
lean_dec_ref_known(v___x_2326_, 1);
v___x_2327_ = lean_box(0);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2310_, v___x_2328_);
v_i_2310_ = v___x_2329_;
v_b_2311_ = v___x_2327_;
goto _start;
}
else
{
lean_dec_ref(v_e_2307_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* v_e_2331_, lean_object* v_as_2332_, lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
size_t v_sz_boxed_2347_; size_t v_i_boxed_2348_; lean_object* v_res_2349_; 
v_sz_boxed_2347_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2348_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2331_, v_as_2332_, v_sz_boxed_2347_, v_i_boxed_2348_, v_b_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v_as_2332_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* v_e_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2377_; 
lean_inc_ref(v_e_2353_);
v___x_2377_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2353_, v_a_2354_, v_a_2358_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; uint8_t v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = lean_unbox(v_a_2378_);
lean_dec(v_a_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_inc_ref(v_e_2353_);
v___x_2380_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2353_, v_a_2354_, v_a_2358_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2488_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2488_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2488_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_unbox(v_a_2381_);
lean_dec(v_a_2381_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_dec_ref(v_e_2353_);
v___x_2386_ = lean_box(0);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2386_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
lean_del_object(v___x_2383_);
lean_inc_ref(v_e_2353_);
v___x_2390_ = l_Lean_Expr_cleanupAnnotations(v_e_2353_);
v___x_2391_ = l_Lean_Expr_isApp(v___x_2390_);
if (v___x_2391_ == 0)
{
lean_dec_ref(v___x_2390_);
lean_dec_ref(v_e_2353_);
goto v___jp_2365_;
}
else
{
lean_object* v_arg_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; 
v_arg_2392_ = lean_ctor_get(v___x_2390_, 1);
lean_inc_ref(v_arg_2392_);
v___x_2393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2390_);
v___x_2394_ = l_Lean_Expr_isApp(v___x_2393_);
if (v___x_2394_ == 0)
{
lean_dec_ref(v___x_2393_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
goto v___jp_2365_;
}
else
{
lean_object* v_arg_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_arg_2395_ = lean_ctor_get(v___x_2393_, 1);
lean_inc_ref(v_arg_2395_);
v___x_2396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2393_);
v___x_2397_ = l_Lean_Expr_isApp(v___x_2396_);
if (v___x_2397_ == 0)
{
lean_dec_ref(v___x_2396_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
goto v___jp_2365_;
}
else
{
lean_object* v_arg_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; 
v_arg_2398_ = lean_ctor_get(v___x_2396_, 1);
lean_inc_ref(v_arg_2398_);
v___x_2433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2396_);
v___x_2434_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2435_ = l_Lean_Expr_isConstOf(v___x_2433_, v___x_2434_);
lean_dec_ref(v___x_2433_);
if (v___x_2435_ == 0)
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
goto v___jp_2365_;
}
else
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__4));
v___x_2486_ = l_Lean_Expr_isConstOf(v_arg_2398_, v___x_2485_);
if (v___x_2486_ == 0)
{
v___y_2437_ = v_a_2354_;
v___y_2438_ = v_a_2355_;
v___y_2439_ = v_a_2356_;
v___y_2440_ = v_a_2357_;
v___y_2441_ = v_a_2358_;
v___y_2442_ = v_a_2359_;
v___y_2443_ = v_a_2360_;
v___y_2444_ = v_a_2361_;
v___y_2445_ = v_a_2362_;
v___y_2446_ = v_a_2363_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2487_; 
lean_inc_ref(v_arg_2392_);
lean_inc_ref(v_arg_2395_);
lean_inc_ref(v_e_2353_);
v___x_2487_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_2353_, v_arg_2395_, v_arg_2392_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_dec_ref_known(v___x_2487_, 1);
v___y_2437_ = v_a_2354_;
v___y_2438_ = v_a_2355_;
v___y_2439_ = v_a_2356_;
v___y_2440_ = v_a_2357_;
v___y_2441_ = v_a_2358_;
v___y_2442_ = v_a_2359_;
v___y_2443_ = v_a_2360_;
v___y_2444_ = v_a_2361_;
v___y_2445_ = v_a_2362_;
v___y_2446_ = v_a_2363_;
goto v___jp_2436_;
}
else
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
return v___x_2487_;
}
}
}
v___jp_2399_:
{
if (v___y_2410_ == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2398_, v___y_2406_, v___y_2408_, v___y_2405_, v___y_2404_, v___y_2407_, v___y_2400_, v___y_2401_, v___y_2403_, v___y_2402_, v___y_2409_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; size_t v_sz_2414_; size_t v___x_2415_; lean_object* v___x_2416_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2413_ = lean_box(0);
v_sz_2414_ = lean_array_size(v_a_2412_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2353_, v_a_2412_, v_sz_2414_, v___x_2415_, v___x_2413_, v___y_2406_, v___y_2408_, v___y_2405_, v___y_2404_, v___y_2407_, v___y_2400_, v___y_2401_, v___y_2403_, v___y_2402_, v___y_2409_);
lean_dec(v_a_2412_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v___x_2416_, 0);
lean_dec(v_unused_2424_);
v___x_2418_ = v___x_2416_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v___x_2416_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2413_);
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2413_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
else
{
return v___x_2416_;
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_e_2353_);
v_a_2425_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2411_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2411_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_e_2353_);
goto v___jp_2371_;
}
}
v___jp_2436_:
{
lean_object* v___x_2447_; 
lean_inc_ref(v_arg_2392_);
lean_inc_ref(v_arg_2395_);
v___x_2447_ = l_Lean_Meta_Grind_Solvers_propagateDiseqs(v_arg_2395_, v_arg_2392_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref_known(v___x_2447_, 1);
lean_inc_ref(v_arg_2398_);
v___x_2448_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2398_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_array_get_size(v_a_2449_);
lean_dec(v_a_2449_);
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_nat_dec_eq(v___x_2450_, v___x_2451_);
if (v___x_2452_ == 0)
{
if (v___x_2435_ == 0)
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
goto v___jp_2368_;
}
else
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2395_, v___y_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2392_, v___y_2437_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
v___x_2458_ = l_Lean_Expr_isAppOf(v_arg_2398_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec(v_a_2456_);
lean_dec(v_a_2454_);
v___y_2400_ = v___y_2442_;
v___y_2401_ = v___y_2443_;
v___y_2402_ = v___y_2445_;
v___y_2403_ = v___y_2444_;
v___y_2404_ = v___y_2440_;
v___y_2405_ = v___y_2439_;
v___y_2406_ = v___y_2437_;
v___y_2407_ = v___y_2441_;
v___y_2408_ = v___y_2438_;
v___y_2409_ = v___y_2446_;
v___y_2410_ = v___x_2458_;
goto v___jp_2399_;
}
else
{
uint8_t v_ctor_2459_; 
v_ctor_2459_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*12 + 2);
lean_dec(v_a_2454_);
if (v_ctor_2459_ == 0)
{
uint8_t v_ctor_2460_; 
v_ctor_2460_ = lean_ctor_get_uint8(v_a_2456_, sizeof(void*)*12 + 2);
lean_dec(v_a_2456_);
v___y_2400_ = v___y_2442_;
v___y_2401_ = v___y_2443_;
v___y_2402_ = v___y_2445_;
v___y_2403_ = v___y_2444_;
v___y_2404_ = v___y_2440_;
v___y_2405_ = v___y_2439_;
v___y_2406_ = v___y_2437_;
v___y_2407_ = v___y_2441_;
v___y_2408_ = v___y_2438_;
v___y_2409_ = v___y_2446_;
v___y_2410_ = v_ctor_2460_;
goto v___jp_2399_;
}
else
{
lean_dec(v_a_2456_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_e_2353_);
goto v___jp_2371_;
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2454_);
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_e_2353_);
v_a_2461_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2455_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2455_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
v_a_2469_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2453_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2453_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
goto v___jp_2368_;
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
v_a_2477_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2448_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2448_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2398_);
lean_dec_ref(v_arg_2395_);
lean_dec_ref(v_arg_2392_);
lean_dec_ref(v_e_2353_);
return v___x_2447_;
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
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v_e_2353_);
v_a_2489_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2380_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2380_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v___x_2497_; uint8_t v___x_2498_; 
lean_inc_ref(v_e_2353_);
v___x_2497_ = l_Lean_Expr_cleanupAnnotations(v_e_2353_);
v___x_2498_ = l_Lean_Expr_isApp(v___x_2497_);
if (v___x_2498_ == 0)
{
lean_dec_ref(v___x_2497_);
lean_dec_ref(v_e_2353_);
goto v___jp_2374_;
}
else
{
lean_object* v_arg_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_arg_2499_ = lean_ctor_get(v___x_2497_, 1);
lean_inc_ref(v_arg_2499_);
v___x_2500_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2497_);
v___x_2501_ = l_Lean_Expr_isApp(v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec_ref(v___x_2500_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
goto v___jp_2374_;
}
else
{
lean_object* v_arg_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v_arg_2502_ = lean_ctor_get(v___x_2500_, 1);
lean_inc_ref(v_arg_2502_);
v___x_2503_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2500_);
v___x_2504_ = l_Lean_Expr_isApp(v___x_2503_);
if (v___x_2504_ == 0)
{
lean_dec_ref(v___x_2503_);
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2503_);
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2507_ = l_Lean_Expr_isConstOf(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2505_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2502_, v_arg_2499_, v_a_2354_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2531_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2531_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2531_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
uint8_t v___x_2513_; 
v___x_2513_ = lean_unbox(v_a_2509_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
lean_del_object(v___x_2511_);
lean_inc_ref(v_e_2353_);
v___x_2514_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2353_, v_a_2515_);
v___x_2517_ = lean_unbox(v_a_2509_);
lean_dec(v_a_2509_);
v___x_2518_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2502_, v_arg_2499_, v___x_2516_, v___x_2517_, v_a_2354_, v_a_2356_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
return v___x_2518_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
v_a_2519_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2514_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2514_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
v___x_2527_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2527_);
v___x_2529_ = v___x_2511_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v_arg_2502_);
lean_dec_ref(v_arg_2499_);
lean_dec_ref(v_e_2353_);
v_a_2532_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2508_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2508_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
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
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v_e_2353_);
v_a_2540_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2377_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2377_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
v___jp_2365_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
v___jp_2368_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
v___jp_2371_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
v___jp_2374_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object* v_e_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_Grind_propagateEqDown(v_e_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec(v_a_2549_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2563_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown___boxed), 12, 0);
v___x_2564_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2562_, v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8____boxed(lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_8_();
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object* v_u_2570_, lean_object* v_00_u03b1_2571_, lean_object* v_binst_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1));
v___x_2579_ = l_Lean_mkConst(v___x_2578_, v_u_2570_);
v___x_2580_ = l_Lean_mkAppB(v___x_2579_, v_00_u03b1_2571_, v_binst_2572_);
v___x_2581_ = lean_box(0);
v___x_2582_ = l_Lean_Meta_synthInstance_x3f(v___x_2580_, v___x_2581_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object* v_u_2583_, lean_object* v_00_u03b1_2584_, lean_object* v_binst_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2583_, v_00_u03b1_2584_, v_binst_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object* v_u_2592_, lean_object* v_00_u03b1_2593_, lean_object* v_binst_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2592_, v_00_u03b1_2593_, v_binst_2594_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object* v_u_2607_, lean_object* v_00_u03b1_2608_, lean_object* v_binst_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(v_u_2607_, v_00_u03b1_2608_, v_binst_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec(v_a_2610_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* v_e_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v___x_2652_; uint8_t v___x_2653_; 
lean_inc_ref(v_e_2637_);
v___x_2652_ = l_Lean_Expr_cleanupAnnotations(v_e_2637_);
v___x_2653_ = l_Lean_Expr_isApp(v___x_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v___x_2652_);
lean_dec_ref(v_e_2637_);
goto v___jp_2649_;
}
else
{
lean_object* v_arg_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_arg_2654_ = lean_ctor_get(v___x_2652_, 1);
lean_inc_ref(v_arg_2654_);
v___x_2655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2652_);
v___x_2656_ = l_Lean_Expr_isApp(v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec_ref(v___x_2655_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
goto v___jp_2649_;
}
else
{
lean_object* v_arg_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_arg_2657_ = lean_ctor_get(v___x_2655_, 1);
lean_inc_ref(v_arg_2657_);
v___x_2658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2655_);
v___x_2659_ = l_Lean_Expr_isApp(v___x_2658_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v___x_2658_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
goto v___jp_2649_;
}
else
{
lean_object* v_arg_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_arg_2660_ = lean_ctor_get(v___x_2658_, 1);
lean_inc_ref(v_arg_2660_);
v___x_2661_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2658_);
v___x_2662_ = l_Lean_Expr_isApp(v___x_2661_);
if (v___x_2662_ == 0)
{
lean_dec_ref(v___x_2661_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
goto v___jp_2649_;
}
else
{
lean_object* v_arg_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v_arg_2663_ = lean_ctor_get(v___x_2661_, 1);
lean_inc_ref(v_arg_2663_);
v___x_2664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2661_);
v___x_2665_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2666_ = l_Lean_Expr_isConstOf(v___x_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v___x_2664_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
goto v___jp_2649_;
}
else
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2657_, v_arg_2654_, v_a_2638_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v_u_2669_; uint8_t v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v_u_2669_ = l_Lean_Expr_constLevels_x21(v___x_2664_);
lean_dec_ref(v___x_2664_);
v___x_2670_ = lean_unbox(v_a_2668_);
lean_dec(v_a_2668_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_inc_ref(v_arg_2654_);
lean_inc_ref(v_arg_2657_);
v___x_2671_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_arg_2657_, v_arg_2654_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2704_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2704_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2704_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
if (lean_obj_tag(v_a_2672_) == 1)
{
lean_object* v_val_2676_; lean_object* v___x_2677_; 
lean_del_object(v___x_2674_);
v_val_2676_ = lean_ctor_get(v_a_2672_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v_a_2672_, 1);
lean_inc_ref(v_arg_2660_);
lean_inc_ref(v_arg_2663_);
lean_inc(v_u_2669_);
v___x_2677_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2669_, v_arg_2663_, v_arg_2660_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2691_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2691_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2691_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
if (lean_obj_tag(v_a_2678_) == 1)
{
lean_object* v_val_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_del_object(v___x_2680_);
v_val_2682_ = lean_ctor_get(v_a_2678_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v_a_2678_, 1);
v___x_2683_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
v___x_2684_ = l_Lean_mkConst(v___x_2683_, v_u_2669_);
v___x_2685_ = l_Lean_mkApp6(v___x_2684_, v_arg_2663_, v_arg_2660_, v_val_2682_, v_arg_2657_, v_arg_2654_, v_val_2676_);
v___x_2686_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_2637_, v___x_2685_, v_a_2638_, v_a_2640_, v_a_2642_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec(v_a_2678_);
lean_dec(v_val_2676_);
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v___x_2687_ = lean_box(0);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2687_);
v___x_2689_ = v___x_2680_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_val_2676_);
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v_a_2692_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2677_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2677_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v_a_2672_);
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v___x_2700_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2700_);
v___x_2702_ = v___x_2674_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v_a_2705_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2671_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2671_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v___x_2713_; 
lean_inc_ref(v_arg_2660_);
lean_inc_ref(v_arg_2663_);
lean_inc(v_u_2669_);
v___x_2713_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2669_, v_arg_2663_, v_arg_2660_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2737_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2737_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2737_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
if (lean_obj_tag(v_a_2714_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2719_; 
lean_del_object(v___x_2716_);
v_val_2718_ = lean_ctor_get(v_a_2714_, 0);
lean_inc(v_val_2718_);
lean_dec_ref_known(v_a_2714_, 1);
lean_inc(v_a_2647_);
lean_inc_ref(v_a_2646_);
lean_inc(v_a_2645_);
lean_inc_ref(v_a_2644_);
lean_inc(v_a_2643_);
lean_inc_ref(v_a_2642_);
lean_inc(v_a_2641_);
lean_inc_ref(v_a_2640_);
lean_inc(v_a_2639_);
lean_inc(v_a_2638_);
lean_inc_ref(v_arg_2654_);
lean_inc_ref(v_arg_2657_);
v___x_2719_ = lean_grind_mk_eq_proof(v_arg_2657_, v_arg_2654_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
v___x_2722_ = l_Lean_mkConst(v___x_2721_, v_u_2669_);
v___x_2723_ = l_Lean_mkApp6(v___x_2722_, v_arg_2663_, v_arg_2660_, v_val_2718_, v_arg_2657_, v_arg_2654_, v_a_2720_);
v___x_2724_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_2637_, v___x_2723_, v_a_2638_, v_a_2640_, v_a_2642_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
return v___x_2724_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_val_2718_);
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v_a_2725_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2719_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2719_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
lean_dec(v_a_2714_);
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v___x_2733_ = lean_box(0);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2733_);
v___x_2735_ = v___x_2716_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_u_2669_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v_a_2738_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2713_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2713_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v___x_2664_);
lean_dec_ref(v_arg_2663_);
lean_dec_ref(v_arg_2660_);
lean_dec_ref(v_arg_2657_);
lean_dec_ref(v_arg_2654_);
lean_dec_ref(v_e_2637_);
v_a_2746_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2667_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2667_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
}
}
v___jp_2649_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_box(0);
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object* v_e_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_Grind_propagateBEqUp(v_e_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec(v_a_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp___boxed), 12, 0);
v___x_2770_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2768_, v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8____boxed(lean_object* v_a_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_8_();
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object* v_e_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___x_2798_; uint8_t v___x_2799_; 
lean_inc_ref(v_e_2783_);
v___x_2798_ = l_Lean_Expr_cleanupAnnotations(v_e_2783_);
v___x_2799_ = l_Lean_Expr_isApp(v___x_2798_);
if (v___x_2799_ == 0)
{
lean_dec_ref(v___x_2798_);
lean_dec_ref(v_e_2783_);
goto v___jp_2795_;
}
else
{
lean_object* v_arg_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v_arg_2800_ = lean_ctor_get(v___x_2798_, 1);
lean_inc_ref(v_arg_2800_);
v___x_2801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2798_);
v___x_2802_ = l_Lean_Expr_isApp(v___x_2801_);
if (v___x_2802_ == 0)
{
lean_dec_ref(v___x_2801_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
goto v___jp_2795_;
}
else
{
lean_object* v_arg_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_arg_2803_ = lean_ctor_get(v___x_2801_, 1);
lean_inc_ref(v_arg_2803_);
v___x_2804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2801_);
v___x_2805_ = l_Lean_Expr_isApp(v___x_2804_);
if (v___x_2805_ == 0)
{
lean_dec_ref(v___x_2804_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
goto v___jp_2795_;
}
else
{
lean_object* v_arg_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v_arg_2806_ = lean_ctor_get(v___x_2804_, 1);
lean_inc_ref(v_arg_2806_);
v___x_2807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2804_);
v___x_2808_ = l_Lean_Expr_isApp(v___x_2807_);
if (v___x_2808_ == 0)
{
lean_dec_ref(v___x_2807_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
goto v___jp_2795_;
}
else
{
lean_object* v_arg_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_arg_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc_ref(v_arg_2809_);
v___x_2810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2807_);
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2812_ = l_Lean_Expr_isConstOf(v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec_ref(v___x_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
goto v___jp_2795_;
}
else
{
lean_object* v___x_2813_; 
lean_inc_ref(v_e_2783_);
v___x_2813_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_2783_, v_a_2784_, v_a_2788_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v_u_2815_; uint8_t v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v_u_2815_ = l_Lean_Expr_constLevels_x21(v___x_2810_);
lean_dec_ref(v___x_2810_);
v___x_2816_ = lean_unbox(v_a_2814_);
lean_dec(v_a_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_inc_ref(v_e_2783_);
v___x_2817_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_2783_, v_a_2784_, v_a_2788_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2900_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2900_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2900_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_unbox(v_a_2818_);
lean_dec(v_a_2818_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v___x_2823_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
else
{
lean_object* v___x_2827_; 
lean_del_object(v___x_2820_);
lean_inc_ref(v_arg_2806_);
lean_inc_ref(v_arg_2809_);
lean_inc(v_u_2815_);
v___x_2827_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2815_, v_arg_2809_, v_arg_2806_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2891_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2891_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2891_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
if (lean_obj_tag(v_a_2828_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2830_);
v_val_2832_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_2828_, 1);
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
v___x_2834_ = lean_box(0);
v___x_2835_ = l_List_head_x21___redArg(v___x_2834_, v_u_2815_);
v___x_2836_ = l_Lean_Level_succ___override(v___x_2835_);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_mkConst(v___x_2833_, v___x_2838_);
lean_inc_ref(v_arg_2800_);
lean_inc_ref(v_arg_2803_);
lean_inc_ref(v_arg_2809_);
v___x_2840_ = l_Lean_mkApp3(v___x_2839_, v_arg_2809_, v_arg_2803_, v_arg_2800_);
v___x_2841_ = l_Lean_Meta_Sym_shareCommon(v___x_2840_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_2803_, v_a_2784_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = lean_box(0);
lean_inc(v_a_2793_);
lean_inc_ref(v_a_2792_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
lean_inc(v_a_2785_);
lean_inc(v_a_2784_);
lean_inc(v_a_2842_);
v___x_2846_ = lean_grind_internalize(v_a_2842_, v_a_2844_, v___x_2845_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v___x_2847_; 
lean_dec_ref_known(v___x_2846_, 1);
v___x_2847_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2788_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
lean_inc(v_a_2793_);
lean_inc_ref(v_a_2792_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
lean_inc(v_a_2785_);
lean_inc(v_a_2784_);
v___x_2849_ = lean_grind_mk_eq_proof(v_e_2783_, v_a_2848_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
v___x_2852_ = l_Lean_mkConst(v___x_2851_, v_u_2815_);
v___x_2853_ = l_Lean_mkApp6(v___x_2852_, v_arg_2809_, v_arg_2806_, v_val_2832_, v_arg_2803_, v_arg_2800_, v_a_2850_);
v___x_2854_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_2842_, v___x_2853_, v_a_2784_, v_a_2786_, v_a_2788_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2854_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2842_);
lean_dec(v_val_2832_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
v_a_2855_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2849_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2849_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2842_);
lean_dec(v_val_2832_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2863_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2847_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2847_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_dec(v_a_2842_);
lean_dec(v_val_2832_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
return v___x_2846_;
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2842_);
lean_dec(v_val_2832_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2871_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2843_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2843_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_val_2832_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2879_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2841_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2841_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
lean_dec(v_a_2828_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v___x_2887_ = lean_box(0);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2887_);
v___x_2889_ = v___x_2830_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2892_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2827_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2827_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2901_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2817_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2817_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v___x_2909_; 
lean_inc_ref(v_arg_2806_);
lean_inc_ref(v_arg_2809_);
lean_inc(v_u_2815_);
v___x_2909_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2815_, v_arg_2809_, v_arg_2806_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2944_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2944_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2944_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
if (lean_obj_tag(v_a_2910_) == 1)
{
lean_object* v_val_2914_; lean_object* v___x_2915_; 
lean_del_object(v___x_2912_);
v_val_2914_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_val_2914_);
lean_dec_ref_known(v_a_2910_, 1);
v___x_2915_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2788_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
lean_inc(v_a_2793_);
lean_inc_ref(v_a_2792_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
lean_inc(v_a_2785_);
lean_inc(v_a_2784_);
v___x_2917_ = lean_grind_mk_eq_proof(v_e_2783_, v_a_2916_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2919_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
v___x_2920_ = l_Lean_mkConst(v___x_2919_, v_u_2815_);
lean_inc_ref(v_arg_2800_);
lean_inc_ref(v_arg_2803_);
v___x_2921_ = l_Lean_mkApp6(v___x_2920_, v_arg_2809_, v_arg_2806_, v_val_2914_, v_arg_2803_, v_arg_2800_, v_a_2918_);
v___x_2922_ = 0;
v___x_2923_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2803_, v_arg_2800_, v___x_2921_, v___x_2922_, v_a_2784_, v_a_2786_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2923_;
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_val_2914_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
v_a_2924_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2917_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2917_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_val_2914_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2932_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2915_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2915_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_a_2910_);
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v___x_2940_ = lean_box(0);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2940_);
v___x_2942_ = v___x_2912_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_u_2815_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2945_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2909_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2909_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v___x_2810_);
lean_dec_ref(v_arg_2809_);
lean_dec_ref(v_arg_2806_);
lean_dec_ref(v_arg_2803_);
lean_dec_ref(v_arg_2800_);
lean_dec_ref(v_e_2783_);
v_a_2953_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2813_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2813_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
}
}
v___jp_2795_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object* v_e_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Meta_Grind_propagateBEqDown(v_e_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec(v_a_2962_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2975_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2976_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqDown___boxed), 12, 0);
v___x_2977_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2975_, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8____boxed(lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_8_();
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* v_e_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_3000_; 
lean_inc_ref(v_e_2985_);
v___x_3000_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2985_, v_a_2986_, v_a_2990_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3038_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3038_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3038_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_unbox(v_a_3001_);
lean_dec(v_a_3001_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_dec_ref(v_e_2985_);
v___x_3006_ = lean_box(0);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3006_);
v___x_3008_ = v___x_3003_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
else
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
lean_del_object(v___x_3003_);
lean_inc_ref(v_e_2985_);
v___x_3010_ = l_Lean_Expr_cleanupAnnotations(v_e_2985_);
v___x_3011_ = l_Lean_Expr_isApp(v___x_3010_);
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3010_);
lean_dec_ref(v_e_2985_);
goto v___jp_2997_;
}
else
{
lean_object* v_arg_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_arg_3012_ = lean_ctor_get(v___x_3010_, 1);
lean_inc_ref(v_arg_3012_);
v___x_3013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3010_);
v___x_3014_ = l_Lean_Expr_isApp(v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec_ref(v___x_3013_);
lean_dec_ref(v_arg_3012_);
lean_dec_ref(v_e_2985_);
goto v___jp_2997_;
}
else
{
lean_object* v_arg_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v_arg_3015_ = lean_ctor_get(v___x_3013_, 1);
lean_inc_ref(v_arg_3015_);
v___x_3016_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3013_);
v___x_3017_ = l_Lean_Expr_isApp(v___x_3016_);
if (v___x_3017_ == 0)
{
lean_dec_ref(v___x_3016_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
lean_dec_ref(v_e_2985_);
goto v___jp_2997_;
}
else
{
lean_object* v_arg_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_arg_3018_ = lean_ctor_get(v___x_3016_, 1);
lean_inc_ref(v_arg_3018_);
v___x_3019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3016_);
v___x_3020_ = l_Lean_Expr_isApp(v___x_3019_);
if (v___x_3020_ == 0)
{
lean_dec_ref(v___x_3019_);
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
lean_dec_ref(v_e_2985_);
goto v___jp_2997_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3021_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3019_);
v___x_3022_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3023_ = l_Lean_Expr_isConstOf(v___x_3021_, v___x_3022_);
lean_dec_ref(v___x_3021_);
if (v___x_3023_ == 0)
{
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_arg_3012_);
lean_dec_ref(v_e_2985_);
goto v___jp_2997_;
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_arg_3012_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v___x_3025_; 
lean_dec_ref_known(v___x_3024_, 1);
lean_inc_ref(v_e_2985_);
v___x_3025_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; lean_object* v___x_3029_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3027_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2985_, v_a_3026_);
v___x_3028_ = 0;
v___x_3029_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3018_, v_arg_3015_, v___x_3027_, v___x_3028_, v_a_2986_, v_a_2988_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
return v___x_3029_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_e_2985_);
v_a_3030_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3025_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3025_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3018_);
lean_dec_ref(v_arg_3015_);
lean_dec_ref(v_e_2985_);
return v___x_3024_;
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
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_e_2985_);
v_a_3039_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3000_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3000_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
v___jp_2997_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object* v_e_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Meta_Grind_propagateEqMatchDown(v_e_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec(v_a_3048_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3062_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown___boxed), 12, 0);
v___x_3063_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3061_, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8____boxed(lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_8_();
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* v_e_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3084_; 
lean_inc_ref(v_e_3069_);
v___x_3084_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3069_, v_a_3070_, v_a_3074_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3119_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3119_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3119_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_unbox(v_a_3085_);
lean_dec(v_a_3085_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
lean_dec_ref(v_e_3069_);
v___x_3090_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3090_);
v___x_3092_ = v___x_3087_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
else
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
lean_del_object(v___x_3087_);
lean_inc_ref(v_e_3069_);
v___x_3094_ = l_Lean_Expr_cleanupAnnotations(v_e_3069_);
v___x_3095_ = l_Lean_Expr_isApp(v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec_ref(v___x_3094_);
lean_dec_ref(v_e_3069_);
goto v___jp_3081_;
}
else
{
lean_object* v_arg_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_arg_3096_ = lean_ctor_get(v___x_3094_, 1);
lean_inc_ref(v_arg_3096_);
v___x_3097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3094_);
v___x_3098_ = l_Lean_Expr_isApp(v___x_3097_);
if (v___x_3098_ == 0)
{
lean_dec_ref(v___x_3097_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_e_3069_);
goto v___jp_3081_;
}
else
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3097_);
v___x_3100_ = l_Lean_Expr_isApp(v___x_3099_);
if (v___x_3100_ == 0)
{
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_e_3069_);
goto v___jp_3081_;
}
else
{
lean_object* v_arg_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_arg_3101_ = lean_ctor_get(v___x_3099_, 1);
lean_inc_ref(v_arg_3101_);
v___x_3102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3099_);
v___x_3103_ = l_Lean_Expr_isApp(v___x_3102_);
if (v___x_3103_ == 0)
{
lean_dec_ref(v___x_3102_);
lean_dec_ref(v_arg_3101_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_e_3069_);
goto v___jp_3081_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3102_);
v___x_3105_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3106_ = l_Lean_Expr_isConstOf(v___x_3104_, v___x_3105_);
lean_dec_ref(v___x_3104_);
if (v___x_3106_ == 0)
{
lean_dec_ref(v_arg_3101_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_e_3069_);
goto v___jp_3081_;
}
else
{
lean_object* v___x_3107_; 
lean_inc_ref(v_e_3069_);
v___x_3107_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3069_, v_a_3108_);
v___x_3110_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3101_, v_arg_3096_, v___x_3109_, v___x_3106_, v_a_3070_, v_a_3072_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3110_;
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v_arg_3101_);
lean_dec_ref(v_arg_3096_);
lean_dec_ref(v_e_3069_);
v_a_3111_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3107_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
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
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_e_3069_);
v_a_3120_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3084_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3084_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
v___jp_3081_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object* v_e_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Meta_Grind_propagateHEqDown(v_e_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec(v_a_3129_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3143_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown___boxed), 12, 0);
v___x_3144_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3142_, v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8____boxed(lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_8_();
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* v_e_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
lean_inc_ref(v_e_3147_);
v___x_3162_ = l_Lean_Expr_cleanupAnnotations(v_e_3147_);
v___x_3163_ = l_Lean_Expr_isApp(v___x_3162_);
if (v___x_3163_ == 0)
{
lean_dec_ref(v___x_3162_);
lean_dec_ref(v_e_3147_);
goto v___jp_3159_;
}
else
{
lean_object* v_arg_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v_arg_3164_ = lean_ctor_get(v___x_3162_, 1);
lean_inc_ref(v_arg_3164_);
v___x_3165_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3162_);
v___x_3166_ = l_Lean_Expr_isApp(v___x_3165_);
if (v___x_3166_ == 0)
{
lean_dec_ref(v___x_3165_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
goto v___jp_3159_;
}
else
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3165_);
v___x_3168_ = l_Lean_Expr_isApp(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v___x_3167_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
goto v___jp_3159_;
}
else
{
lean_object* v_arg_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_arg_3169_ = lean_ctor_get(v___x_3167_, 1);
lean_inc_ref(v_arg_3169_);
v___x_3170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3167_);
v___x_3171_ = l_Lean_Expr_isApp(v___x_3170_);
if (v___x_3171_ == 0)
{
lean_dec_ref(v___x_3170_);
lean_dec_ref(v_arg_3169_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
goto v___jp_3159_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3170_);
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3174_ = l_Lean_Expr_isConstOf(v___x_3172_, v___x_3173_);
lean_dec_ref(v___x_3172_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v_arg_3169_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
goto v___jp_3159_;
}
else
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_3169_, v_arg_3164_, v_a_3148_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3197_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3197_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3197_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_unbox(v_a_3176_);
lean_dec(v_a_3176_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_dec_ref(v_arg_3169_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
v___x_3181_ = lean_box(0);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
else
{
lean_object* v___x_3185_; 
lean_del_object(v___x_3178_);
lean_inc(v_a_3157_);
lean_inc_ref(v_a_3156_);
lean_inc(v_a_3155_);
lean_inc_ref(v_a_3154_);
lean_inc(v_a_3153_);
lean_inc_ref(v_a_3152_);
lean_inc(v_a_3151_);
lean_inc_ref(v_a_3150_);
lean_inc(v_a_3149_);
lean_inc(v_a_3148_);
v___x_3185_ = lean_grind_mk_heq_proof(v_arg_3169_, v_arg_3164_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
lean_inc_ref(v_e_3147_);
v___x_3187_ = l_Lean_Meta_mkEqTrueCore(v_e_3147_, v_a_3186_);
v___x_3188_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3147_, v___x_3187_, v_a_3148_, v_a_3150_, v_a_3152_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
return v___x_3188_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v_e_3147_);
v_a_3189_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3185_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3185_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_arg_3169_);
lean_dec_ref(v_arg_3164_);
lean_dec_ref(v_e_3147_);
v_a_3198_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3175_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3175_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
}
}
v___jp_3159_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object* v_e_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Meta_Grind_propagateHEqUp(v_e_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3221_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp___boxed), 12, 0);
v___x_3222_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3220_, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8____boxed(lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_8_();
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object* v_e_3225_, lean_object* v_args_3226_, uint8_t v_ite_3227_, lean_object* v_rhs_3228_, lean_object* v_h_3229_, lean_object* v_i_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3242_ = lean_array_get_size(v_args_3226_);
v___x_3243_ = lean_nat_dec_lt(v_i_3230_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_dec(v_i_3230_);
v___x_3244_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_rhs_3228_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3225_, v_a_3231_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
lean_inc_ref(v_e_3225_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_e_3225_);
lean_inc(v_a_3240_);
lean_inc_ref(v_a_3239_);
lean_inc(v_a_3238_);
lean_inc_ref(v_a_3237_);
lean_inc(v_a_3236_);
lean_inc_ref(v_a_3235_);
lean_inc(v_a_3234_);
lean_inc_ref(v_a_3233_);
lean_inc(v_a_3232_);
lean_inc(v_a_3231_);
lean_inc(v_a_3245_);
v___x_3249_ = lean_grind_internalize(v_a_3245_, v_a_3247_, v___x_3248_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_dec_ref_known(v___x_3249_, 1);
if (v_ite_3227_ == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3225_, v_a_3245_, v_h_3229_, v___x_3243_, v_a_3231_, v_a_3233_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; 
lean_inc(v_a_3245_);
lean_inc_ref(v_e_3225_);
v___x_3251_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3225_, v_a_3245_, v_a_3231_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v___x_3252_; 
lean_dec_ref_known(v___x_3251_, 1);
v___x_3252_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3225_, v_a_3245_, v_h_3229_, v___x_3243_, v_a_3231_, v_a_3233_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
return v___x_3252_;
}
else
{
lean_dec(v_a_3245_);
lean_dec_ref(v_h_3229_);
lean_dec_ref(v_e_3225_);
return v___x_3251_;
}
}
}
else
{
lean_dec(v_a_3245_);
lean_dec_ref(v_h_3229_);
lean_dec_ref(v_e_3225_);
return v___x_3249_;
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_a_3245_);
lean_dec_ref(v_h_3229_);
lean_dec_ref(v_e_3225_);
v_a_3253_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3246_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3246_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v_h_3229_);
lean_dec_ref(v_e_3225_);
v_a_3261_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3244_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3244_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
lean_object* v_arg_3269_; lean_object* v_rhs_x27_3270_; lean_object* v___x_3271_; 
v_arg_3269_ = lean_array_fget_borrowed(v_args_3226_, v_i_3230_);
lean_inc_n(v_arg_3269_, 2);
v_rhs_x27_3270_ = l_Lean_Expr_app___override(v_rhs_3228_, v_arg_3269_);
v___x_3271_ = l_Lean_Meta_mkCongrFun(v_h_3229_, v_arg_3269_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = lean_unsigned_to_nat(1u);
v___x_3274_ = lean_nat_add(v_i_3230_, v___x_3273_);
lean_dec(v_i_3230_);
v_rhs_3228_ = v_rhs_x27_3270_;
v_h_3229_ = v_a_3272_;
v_i_3230_ = v___x_3274_;
goto _start;
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v_rhs_x27_3270_);
lean_dec(v_i_3230_);
lean_dec_ref(v_e_3225_);
v_a_3276_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3271_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3271_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object** _args){
lean_object* v_e_3284_ = _args[0];
lean_object* v_args_3285_ = _args[1];
lean_object* v_ite_3286_ = _args[2];
lean_object* v_rhs_3287_ = _args[3];
lean_object* v_h_3288_ = _args[4];
lean_object* v_i_3289_ = _args[5];
lean_object* v_a_3290_ = _args[6];
lean_object* v_a_3291_ = _args[7];
lean_object* v_a_3292_ = _args[8];
lean_object* v_a_3293_ = _args[9];
lean_object* v_a_3294_ = _args[10];
lean_object* v_a_3295_ = _args[11];
lean_object* v_a_3296_ = _args[12];
lean_object* v_a_3297_ = _args[13];
lean_object* v_a_3298_ = _args[14];
lean_object* v_a_3299_ = _args[15];
lean_object* v_a_3300_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3301_; lean_object* v_res_3302_; 
v_ite_boxed_3301_ = lean_unbox(v_ite_3286_);
v_res_3302_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3284_, v_args_3285_, v_ite_boxed_3301_, v_rhs_3287_, v_h_3288_, v_i_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec_ref(v_a_3292_);
lean_dec(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_args_3285_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object* v_e_3303_, lean_object* v_rhs_3304_, lean_object* v_h_3305_, lean_object* v_prefixSize_3306_, lean_object* v_args_3307_, uint8_t v_ite_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = lean_array_get_size(v_args_3307_);
v___x_3330_ = lean_nat_dec_eq(v_prefixSize_3306_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3303_, v_args_3307_, v_ite_3308_, v_rhs_3304_, v_h_3305_, v_prefixSize_3306_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; 
lean_dec(v_prefixSize_3306_);
v___x_3332_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3303_, v_a_3309_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
lean_inc_ref(v_e_3303_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_e_3303_);
lean_inc(v_a_3318_);
lean_inc_ref(v_a_3317_);
lean_inc(v_a_3316_);
lean_inc_ref(v_a_3315_);
lean_inc(v_a_3314_);
lean_inc_ref(v_a_3313_);
lean_inc(v_a_3312_);
lean_inc_ref(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc(v_a_3309_);
lean_inc_ref(v_rhs_3304_);
v___x_3335_ = lean_grind_internalize(v_rhs_3304_, v_a_3333_, v___x_3334_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_dec_ref_known(v___x_3335_, 1);
if (v_ite_3308_ == 0)
{
v___y_3321_ = v_a_3309_;
v___y_3322_ = v_a_3311_;
v___y_3323_ = v_a_3315_;
v___y_3324_ = v_a_3316_;
v___y_3325_ = v_a_3317_;
v___y_3326_ = v_a_3318_;
goto v___jp_3320_;
}
else
{
lean_object* v___x_3336_; 
lean_inc_ref(v_rhs_3304_);
lean_inc_ref(v_e_3303_);
v___x_3336_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3303_, v_rhs_3304_, v_a_3309_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_dec_ref_known(v___x_3336_, 1);
v___y_3321_ = v_a_3309_;
v___y_3322_ = v_a_3311_;
v___y_3323_ = v_a_3315_;
v___y_3324_ = v_a_3316_;
v___y_3325_ = v_a_3317_;
v___y_3326_ = v_a_3318_;
goto v___jp_3320_;
}
else
{
lean_dec_ref(v_h_3305_);
lean_dec_ref(v_rhs_3304_);
lean_dec_ref(v_e_3303_);
return v___x_3336_;
}
}
}
else
{
lean_dec_ref(v_h_3305_);
lean_dec_ref(v_rhs_3304_);
lean_dec_ref(v_e_3303_);
return v___x_3335_;
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v_h_3305_);
lean_dec_ref(v_rhs_3304_);
lean_dec_ref(v_e_3303_);
v_a_3337_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3332_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3332_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
v___jp_3320_:
{
uint8_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = 0;
v___x_3328_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3303_, v_rhs_3304_, v_h_3305_, v___x_3327_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object** _args){
lean_object* v_e_3345_ = _args[0];
lean_object* v_rhs_3346_ = _args[1];
lean_object* v_h_3347_ = _args[2];
lean_object* v_prefixSize_3348_ = _args[3];
lean_object* v_args_3349_ = _args[4];
lean_object* v_ite_3350_ = _args[5];
lean_object* v_a_3351_ = _args[6];
lean_object* v_a_3352_ = _args[7];
lean_object* v_a_3353_ = _args[8];
lean_object* v_a_3354_ = _args[9];
lean_object* v_a_3355_ = _args[10];
lean_object* v_a_3356_ = _args[11];
lean_object* v_a_3357_ = _args[12];
lean_object* v_a_3358_ = _args[13];
lean_object* v_a_3359_ = _args[14];
lean_object* v_a_3360_ = _args[15];
lean_object* v_a_3361_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3362_; lean_object* v_res_3363_; 
v_ite_boxed_3362_ = lean_unbox(v_ite_3350_);
v_res_3363_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3345_, v_rhs_3346_, v_h_3347_, v_prefixSize_3348_, v_args_3349_, v_ite_boxed_3362_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_args_3349_);
return v_res_3363_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateIte___closed__0(void){
_start:
{
lean_object* v___x_3364_; lean_object* v_dummy_3365_; 
v___x_3364_ = lean_box(0);
v_dummy_3365_ = l_Lean_Expr_sort___override(v___x_3364_);
return v_dummy_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* v_e_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_numArgs_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_numArgs_3384_ = l_Lean_Expr_getAppNumArgs(v_e_3372_);
v___x_3385_ = lean_unsigned_to_nat(5u);
v___x_3386_ = lean_nat_dec_lt(v_numArgs_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v_c_3390_; lean_object* v___x_3391_; 
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = lean_nat_sub(v_numArgs_3384_, v___x_3387_);
v___x_3389_ = lean_nat_sub(v___x_3388_, v___x_3387_);
v_c_3390_ = l_Lean_Expr_getRevArg_x21(v_e_3372_, v___x_3389_);
lean_inc_ref(v_c_3390_);
v___x_3391_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3390_, v_a_3373_, v_a_3377_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; uint8_t v___x_3393_; uint8_t v___x_3394_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = 1;
v___x_3394_ = lean_unbox(v_a_3392_);
lean_dec(v_a_3392_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_inc_ref(v_c_3390_);
v___x_3395_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3390_, v_a_3373_, v_a_3377_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3429_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3429_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3429_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_unbox(v_a_3396_);
lean_dec(v_a_3396_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
lean_dec_ref(v_c_3390_);
lean_dec(v___x_3388_);
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v___x_3401_ = lean_box(0);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3401_);
v___x_3403_ = v___x_3398_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
lean_object* v___x_3405_; 
lean_del_object(v___x_3398_);
v___x_3405_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3390_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v_dummy_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = l_Lean_Expr_getAppFn(v_e_3372_);
v___x_3408_ = l_Lean_instInhabitedExpr;
v_dummy_3409_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3410_ = lean_mk_array(v_numArgs_3384_, v_dummy_3409_);
lean_inc_ref(v_e_3372_);
v___x_3411_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3372_, v___x_3410_, v___x_3388_);
v___x_3412_ = lean_unsigned_to_nat(4u);
v___x_3413_ = lean_array_get(v___x_3408_, v___x_3411_, v___x_3412_);
v___x_3414_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
v___x_3415_ = l_Lean_Expr_constLevels_x21(v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3416_ = l_Lean_mkConst(v___x_3414_, v___x_3415_);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = l_Lean_mkAppRange(v___x_3416_, v___x_3417_, v___x_3385_, v___x_3411_);
v___x_3419_ = l_Lean_Expr_app___override(v___x_3418_, v_a_3406_);
v___x_3420_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3372_, v___x_3413_, v___x_3419_, v___x_3385_, v___x_3411_, v___x_3393_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
lean_dec_ref(v___x_3411_);
return v___x_3420_;
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v___x_3388_);
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v_a_3421_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3405_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3405_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_c_3390_);
lean_dec(v___x_3388_);
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v_a_3430_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3395_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3395_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3390_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v_dummy_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = l_Lean_Expr_getAppFn(v_e_3372_);
v___x_3441_ = l_Lean_instInhabitedExpr;
v_dummy_3442_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3443_ = lean_mk_array(v_numArgs_3384_, v_dummy_3442_);
lean_inc_ref(v_e_3372_);
v___x_3444_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3372_, v___x_3443_, v___x_3388_);
v___x_3445_ = lean_unsigned_to_nat(3u);
v___x_3446_ = lean_array_get(v___x_3441_, v___x_3444_, v___x_3445_);
v___x_3447_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__4));
v___x_3448_ = l_Lean_Expr_constLevels_x21(v___x_3440_);
lean_dec_ref(v___x_3440_);
v___x_3449_ = l_Lean_mkConst(v___x_3447_, v___x_3448_);
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = l_Lean_mkAppRange(v___x_3449_, v___x_3450_, v___x_3385_, v___x_3444_);
v___x_3452_ = l_Lean_Expr_app___override(v___x_3451_, v_a_3439_);
v___x_3453_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3372_, v___x_3446_, v___x_3452_, v___x_3385_, v___x_3444_, v___x_3393_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
lean_dec_ref(v___x_3444_);
return v___x_3453_;
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v___x_3388_);
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v_a_3454_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3438_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3438_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_c_3390_);
lean_dec(v___x_3388_);
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v_a_3462_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3391_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3391_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_numArgs_3384_);
lean_dec_ref(v_e_3372_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object* v_e_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_Meta_Grind_propagateIte(v_e_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec(v_a_3473_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_));
v___x_3490_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte___boxed), 12, 0);
v___x_3491_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3489_, v___x_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8____boxed(lean_object* v_a_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1746658988____hygCtx___hyg_8_();
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* v_e_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_numArgs_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v_numArgs_3516_ = l_Lean_Expr_getAppNumArgs(v_e_3504_);
v___x_3517_ = lean_unsigned_to_nat(5u);
v___x_3518_ = lean_nat_dec_lt(v_numArgs_3516_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v_c_3522_; lean_object* v___x_3523_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_sub(v_numArgs_3516_, v___x_3519_);
v___x_3521_ = lean_nat_sub(v___x_3520_, v___x_3519_);
v_c_3522_ = l_Lean_Expr_getRevArg_x21(v_e_3504_, v___x_3521_);
lean_inc_ref(v_c_3522_);
v___x_3523_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3522_, v_a_3505_, v_a_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; uint8_t v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = lean_unbox(v_a_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_inc_ref(v_c_3522_);
v___x_3526_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3522_, v_a_3505_, v_a_3509_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3584_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3584_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3584_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
uint8_t v___x_3531_; 
v___x_3531_ = lean_unbox(v_a_3527_);
lean_dec(v_a_3527_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
lean_dec(v_a_3524_);
lean_dec_ref(v_c_3522_);
lean_dec(v___x_3520_);
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v___x_3532_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3532_);
v___x_3534_ = v___x_3529_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
else
{
lean_object* v___x_3536_; 
lean_del_object(v___x_3529_);
lean_inc_ref(v_c_3522_);
v___x_3536_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3522_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; lean_object* v_dummy_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc_n(v_a_3537_, 2);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_Expr_getAppFn(v_e_3504_);
v_dummy_3539_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3540_ = lean_mk_array(v_numArgs_3516_, v_dummy_3539_);
lean_inc_ref(v_e_3504_);
v___x_3541_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3504_, v___x_3540_, v___x_3520_);
v___x_3542_ = l_Lean_instInhabitedExpr;
v___x_3543_ = lean_unsigned_to_nat(4u);
v___x_3544_ = lean_array_get(v___x_3542_, v___x_3541_, v___x_3543_);
v___x_3545_ = l_Lean_Meta_mkOfEqFalseCore(v_c_3522_, v_a_3537_);
v___x_3546_ = l_Lean_Expr_app___override(v___x_3544_, v___x_3545_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
lean_inc(v_a_3508_);
lean_inc_ref(v_a_3507_);
lean_inc(v_a_3506_);
lean_inc(v_a_3505_);
v___x_3547_ = lean_grind_preprocess(v___x_3546_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_expr_3549_; lean_object* v___x_3550_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v_expr_3549_ = lean_ctor_get(v_a_3548_, 0);
lean_inc_ref(v_expr_3549_);
v___x_3550_ = l_Lean_Meta_Simp_Result_getProof(v_a_3548_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
v___x_3553_ = l_Lean_Expr_constLevels_x21(v___x_3538_);
lean_dec_ref(v___x_3538_);
v___x_3554_ = l_Lean_mkConst(v___x_3552_, v___x_3553_);
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = l_Lean_mkAppRange(v___x_3554_, v___x_3555_, v___x_3517_, v___x_3541_);
lean_inc_ref(v_expr_3549_);
v___x_3557_ = l_Lean_mkApp3(v___x_3556_, v_expr_3549_, v_a_3537_, v_a_3551_);
v___x_3558_ = lean_unbox(v_a_3524_);
lean_dec(v_a_3524_);
v___x_3559_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3504_, v_expr_3549_, v___x_3557_, v___x_3517_, v___x_3541_, v___x_3558_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
lean_dec_ref(v___x_3541_);
return v___x_3559_;
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec_ref(v_expr_3549_);
lean_dec_ref(v___x_3541_);
lean_dec_ref(v___x_3538_);
lean_dec(v_a_3537_);
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3504_);
v_a_3560_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3550_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3550_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec_ref(v___x_3541_);
lean_dec_ref(v___x_3538_);
lean_dec(v_a_3537_);
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3504_);
v_a_3568_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3547_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3547_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_a_3524_);
lean_dec_ref(v_c_3522_);
lean_dec(v___x_3520_);
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v_a_3576_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3536_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3536_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_a_3524_);
lean_dec_ref(v_c_3522_);
lean_dec(v___x_3520_);
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v_a_3585_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3526_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3526_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v___x_3593_; 
lean_dec(v_a_3524_);
lean_inc_ref(v_c_3522_);
v___x_3593_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3522_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v_dummy_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_n(v_a_3594_, 2);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = l_Lean_Expr_getAppFn(v_e_3504_);
v_dummy_3596_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3597_ = lean_mk_array(v_numArgs_3516_, v_dummy_3596_);
lean_inc_ref(v_e_3504_);
v___x_3598_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3504_, v___x_3597_, v___x_3520_);
v___x_3599_ = l_Lean_instInhabitedExpr;
v___x_3600_ = lean_unsigned_to_nat(3u);
v___x_3601_ = lean_array_get(v___x_3599_, v___x_3598_, v___x_3600_);
v___x_3602_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3522_, v_a_3594_);
v___x_3603_ = l_Lean_Expr_app___override(v___x_3601_, v___x_3602_);
lean_inc(v_a_3514_);
lean_inc_ref(v_a_3513_);
lean_inc(v_a_3512_);
lean_inc_ref(v_a_3511_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
lean_inc(v_a_3508_);
lean_inc_ref(v_a_3507_);
lean_inc(v_a_3506_);
lean_inc(v_a_3505_);
v___x_3604_ = lean_grind_preprocess(v___x_3603_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v_expr_3606_; lean_object* v___x_3607_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v_expr_3606_ = lean_ctor_get(v_a_3605_, 0);
lean_inc_ref(v_expr_3606_);
v___x_3607_ = l_Lean_Meta_Simp_Result_getProof(v_a_3605_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__3));
v___x_3610_ = l_Lean_Expr_constLevels_x21(v___x_3595_);
lean_dec_ref(v___x_3595_);
v___x_3611_ = l_Lean_mkConst(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = l_Lean_mkAppRange(v___x_3611_, v___x_3612_, v___x_3517_, v___x_3598_);
lean_inc_ref(v_expr_3606_);
v___x_3614_ = l_Lean_mkApp3(v___x_3613_, v_expr_3606_, v_a_3594_, v_a_3608_);
v___x_3615_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3504_, v_expr_3606_, v___x_3614_, v___x_3517_, v___x_3598_, v___x_3518_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
lean_dec_ref(v___x_3598_);
return v___x_3615_;
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v_expr_3606_);
lean_dec_ref(v___x_3598_);
lean_dec_ref(v___x_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_e_3504_);
v_a_3616_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3607_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3607_);
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
lean_dec_ref(v___x_3598_);
lean_dec_ref(v___x_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_e_3504_);
v_a_3624_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3604_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3604_);
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
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v_c_3522_);
lean_dec(v___x_3520_);
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v_a_3632_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3593_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3593_);
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
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v_c_3522_);
lean_dec(v___x_3520_);
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v_a_3640_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3523_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3523_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v_numArgs_3516_);
lean_dec_ref(v_e_3504_);
v___x_3648_ = lean_box(0);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object* v_e_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_Meta_Grind_propagateDIte(v_e_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec(v_a_3651_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_));
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte___boxed), 12, 0);
v___x_3669_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3667_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8____boxed(lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_8_();
return v_res_3671_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_box(0);
v___x_3691_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__8));
v___x_3692_ = l_Lean_mkConst(v___x_3691_, v___x_3690_);
return v___x_3692_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = lean_box(0);
v___x_3699_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__11));
v___x_3700_ = l_Lean_mkConst(v___x_3699_, v___x_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* v_e_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3716_; 
lean_inc_ref(v_e_3701_);
v___x_3716_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_3701_, v_a_3702_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3770_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3770_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3770_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
uint8_t v_ctor_3721_; 
v_ctor_3721_ = lean_ctor_get_uint8(v_a_3717_, sizeof(void*)*12 + 2);
if (v_ctor_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_dec(v_a_3717_);
lean_dec_ref(v_e_3701_);
v___x_3722_ = lean_box(0);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3722_);
v___x_3724_ = v___x_3719_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
else
{
lean_object* v_self_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v_self_3726_ = lean_ctor_get(v_a_3717_, 0);
lean_inc_ref(v_self_3726_);
lean_dec(v_a_3717_);
lean_inc_ref(v_e_3701_);
v___x_3727_ = l_Lean_Expr_cleanupAnnotations(v_e_3701_);
v___x_3728_ = l_Lean_Expr_isApp(v___x_3727_);
if (v___x_3728_ == 0)
{
lean_dec_ref(v___x_3727_);
lean_dec_ref(v_self_3726_);
lean_del_object(v___x_3719_);
lean_dec_ref(v_e_3701_);
goto v___jp_3713_;
}
else
{
lean_object* v_arg_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v_arg_3729_ = lean_ctor_get(v___x_3727_, 1);
lean_inc_ref(v_arg_3729_);
v___x_3730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3727_);
v___x_3731_ = l_Lean_Expr_isApp(v___x_3730_);
if (v___x_3731_ == 0)
{
lean_dec_ref(v___x_3730_);
lean_dec_ref(v_arg_3729_);
lean_dec_ref(v_self_3726_);
lean_del_object(v___x_3719_);
lean_dec_ref(v_e_3701_);
goto v___jp_3713_;
}
else
{
lean_object* v_arg_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_arg_3732_ = lean_ctor_get(v___x_3730_, 1);
lean_inc_ref(v_arg_3732_);
v___x_3733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3730_);
v___x_3734_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3735_ = l_Lean_Expr_isConstOf(v___x_3733_, v___x_3734_);
lean_dec_ref(v___x_3733_);
if (v___x_3735_ == 0)
{
lean_dec_ref(v_arg_3732_);
lean_dec_ref(v_arg_3729_);
lean_dec_ref(v_self_3726_);
lean_del_object(v___x_3719_);
lean_dec_ref(v_e_3701_);
goto v___jp_3713_;
}
else
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
v___x_3737_ = l_Lean_Expr_isConstOf(v_self_3726_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3738_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
v___x_3739_ = l_Lean_Expr_isConstOf(v_self_3726_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec_ref(v_arg_3732_);
lean_dec_ref(v_arg_3729_);
lean_dec_ref(v_self_3726_);
lean_dec_ref(v_e_3701_);
v___x_3740_ = lean_box(0);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3740_);
v___x_3742_ = v___x_3719_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
else
{
lean_object* v___x_3744_; 
lean_del_object(v___x_3719_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
lean_inc(v_a_3709_);
lean_inc_ref(v_a_3708_);
lean_inc(v_a_3707_);
lean_inc_ref(v_a_3706_);
lean_inc(v_a_3705_);
lean_inc_ref(v_a_3704_);
lean_inc(v_a_3703_);
lean_inc(v_a_3702_);
v___x_3744_ = lean_grind_mk_eq_proof(v_e_3701_, v_self_3726_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
v___x_3746_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__9, &l_Lean_Meta_Grind_propagateDecideDown___closed__9_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9);
lean_inc_ref(v_arg_3732_);
v___x_3747_ = l_Lean_mkApp3(v___x_3746_, v_arg_3732_, v_arg_3729_, v_a_3745_);
v___x_3748_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_3732_, v___x_3747_, v_a_3702_, v_a_3704_, v_a_3706_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
return v___x_3748_;
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v_arg_3732_);
lean_dec_ref(v_arg_3729_);
v_a_3749_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3744_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3744_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
else
{
lean_object* v___x_3757_; 
lean_del_object(v___x_3719_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
lean_inc(v_a_3709_);
lean_inc_ref(v_a_3708_);
lean_inc(v_a_3707_);
lean_inc_ref(v_a_3706_);
lean_inc(v_a_3705_);
lean_inc_ref(v_a_3704_);
lean_inc(v_a_3703_);
lean_inc(v_a_3702_);
v___x_3757_ = lean_grind_mk_eq_proof(v_e_3701_, v_self_3726_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___x_3759_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__12, &l_Lean_Meta_Grind_propagateDecideDown___closed__12_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12);
lean_inc_ref(v_arg_3732_);
v___x_3760_ = l_Lean_mkApp3(v___x_3759_, v_arg_3732_, v_arg_3729_, v_a_3758_);
v___x_3761_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_3732_, v___x_3760_, v_a_3702_, v_a_3704_, v_a_3706_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
return v___x_3761_;
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_arg_3732_);
lean_dec_ref(v_arg_3729_);
v_a_3762_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3757_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3757_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
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
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_e_3701_);
v_a_3771_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3716_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3716_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
v___jp_3713_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object* v_e_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Meta_Grind_propagateDecideDown(v_e_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
lean_dec(v_a_3780_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3794_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown___boxed), 12, 0);
v___x_3795_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3793_, v___x_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8____boxed(lean_object* v_a_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_8_();
return v_res_3797_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_box(0);
v___x_3804_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__1));
v___x_3805_ = l_Lean_mkConst(v___x_3804_, v___x_3803_);
return v___x_3805_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = lean_box(0);
v___x_3812_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__4));
v___x_3813_ = l_Lean_mkConst(v___x_3812_, v___x_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* v_e_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
lean_inc_ref(v_e_3814_);
v___x_3829_ = l_Lean_Expr_cleanupAnnotations(v_e_3814_);
v___x_3830_ = l_Lean_Expr_isApp(v___x_3829_);
if (v___x_3830_ == 0)
{
lean_dec_ref(v___x_3829_);
lean_dec_ref(v_e_3814_);
goto v___jp_3826_;
}
else
{
lean_object* v_arg_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_arg_3831_ = lean_ctor_get(v___x_3829_, 1);
lean_inc_ref(v_arg_3831_);
v___x_3832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3829_);
v___x_3833_ = l_Lean_Expr_isApp(v___x_3832_);
if (v___x_3833_ == 0)
{
lean_dec_ref(v___x_3832_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
goto v___jp_3826_;
}
else
{
lean_object* v_arg_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; uint8_t v___x_3837_; 
v_arg_3834_ = lean_ctor_get(v___x_3832_, 1);
lean_inc_ref(v_arg_3834_);
v___x_3835_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3832_);
v___x_3836_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3837_ = l_Lean_Expr_isConstOf(v___x_3835_, v___x_3836_);
lean_dec_ref(v___x_3835_);
if (v___x_3837_ == 0)
{
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
goto v___jp_3826_;
}
else
{
lean_object* v___x_3838_; 
lean_inc_ref(v_arg_3834_);
v___x_3838_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_3834_, v_a_3815_, v_a_3819_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; uint8_t v___x_3840_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = lean_unbox(v_a_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
lean_inc_ref(v_arg_3834_);
v___x_3841_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_3834_, v_a_3815_, v_a_3819_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3875_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3875_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3875_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_unbox(v_a_3842_);
lean_dec(v_a_3842_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
lean_dec(v_a_3839_);
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v___x_3847_ = lean_box(0);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 0, v___x_3847_);
v___x_3849_ = v___x_3844_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
else
{
lean_object* v___x_3851_; 
lean_del_object(v___x_3844_);
v___x_3851_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3819_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3853_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
lean_inc_ref(v_arg_3834_);
v___x_3853_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_3834_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3855_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__2, &l_Lean_Meta_Grind_propagateDecideUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2);
v___x_3856_ = l_Lean_mkApp3(v___x_3855_, v_arg_3834_, v_arg_3831_, v_a_3854_);
v___x_3857_ = lean_unbox(v_a_3839_);
lean_dec(v_a_3839_);
v___x_3858_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3814_, v_a_3852_, v___x_3856_, v___x_3857_, v_a_3815_, v_a_3817_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
return v___x_3858_;
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_a_3852_);
lean_dec(v_a_3839_);
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3859_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3853_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3853_);
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
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec(v_a_3839_);
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3867_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3851_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3851_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3883_; 
lean_dec(v_a_3839_);
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3876_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3878_ = v___x_3841_;
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3841_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3883_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3881_; 
if (v_isShared_3879_ == 0)
{
v___x_3881_ = v___x_3878_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v___x_3884_; 
lean_dec(v_a_3839_);
v___x_3884_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3819_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
lean_inc_ref(v_arg_3834_);
v___x_3886_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_3834_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__5, &l_Lean_Meta_Grind_propagateDecideUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5);
v___x_3889_ = l_Lean_mkApp3(v___x_3888_, v_arg_3834_, v_arg_3831_, v_a_3887_);
v___x_3890_ = 0;
v___x_3891_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3814_, v_a_3885_, v___x_3889_, v___x_3890_, v_a_3815_, v_a_3817_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
return v___x_3891_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v_a_3885_);
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3892_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3886_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3886_);
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
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3900_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3884_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3884_);
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
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_arg_3834_);
lean_dec_ref(v_arg_3831_);
lean_dec_ref(v_e_3814_);
v_a_3908_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3838_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3838_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
v___jp_3826_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = lean_box(0);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
return v___x_3828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object* v_e_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_Meta_Grind_propagateDecideUp(v_e_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec(v_a_3917_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3930_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3931_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp___boxed), 12, 0);
v___x_3932_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3930_, v___x_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8____boxed(lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_8_();
return v_res_3934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_box(0);
v___x_3945_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__2));
v___x_3946_ = l_Lean_mkConst(v___x_3945_, v___x_3944_);
return v___x_3946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = lean_box(0);
v___x_3953_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__4));
v___x_3954_ = l_Lean_mkConst(v___x_3953_, v___x_3952_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__6));
v___x_3962_ = l_Lean_mkConst(v___x_3961_, v___x_3960_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_box(0);
v___x_3969_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__8));
v___x_3970_ = l_Lean_mkConst(v___x_3969_, v___x_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* v_e_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v___x_3986_; uint8_t v___x_3987_; 
lean_inc_ref(v_e_3971_);
v___x_3986_ = l_Lean_Expr_cleanupAnnotations(v_e_3971_);
v___x_3987_ = l_Lean_Expr_isApp(v___x_3986_);
if (v___x_3987_ == 0)
{
lean_dec_ref(v___x_3986_);
lean_dec_ref(v_e_3971_);
goto v___jp_3983_;
}
else
{
lean_object* v_arg_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; 
v_arg_3988_ = lean_ctor_get(v___x_3986_, 1);
lean_inc_ref(v_arg_3988_);
v___x_3989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3986_);
v___x_3990_ = l_Lean_Expr_isApp(v___x_3989_);
if (v___x_3990_ == 0)
{
lean_dec_ref(v___x_3989_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
goto v___jp_3983_;
}
else
{
lean_object* v_arg_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_arg_3991_ = lean_ctor_get(v___x_3989_, 1);
lean_inc_ref(v_arg_3991_);
v___x_3992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3989_);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_3994_ = l_Lean_Expr_isConstOf(v___x_3992_, v___x_3993_);
lean_dec_ref(v___x_3992_);
if (v___x_3994_ == 0)
{
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
goto v___jp_3983_;
}
else
{
lean_object* v___x_3995_; 
lean_inc_ref(v_arg_3991_);
v___x_3995_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3991_, v_a_3972_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; uint8_t v___x_3997_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
v___x_3997_ = lean_unbox(v_a_3996_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; 
lean_inc_ref(v_arg_3988_);
v___x_3998_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_3988_, v_a_3972_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; uint8_t v___x_4000_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = lean_unbox(v_a_3999_);
lean_dec(v_a_3999_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v_a_3996_);
lean_inc_ref(v_arg_3991_);
v___x_4001_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3991_, v_a_3972_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; uint8_t v___x_4003_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v___x_4003_ = lean_unbox(v_a_4002_);
lean_dec(v_a_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
lean_inc_ref(v_arg_3988_);
v___x_4004_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_3988_, v_a_3972_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4027_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4027_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4027_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_unbox(v_a_4005_);
lean_dec(v_a_4005_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4012_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v___x_4010_ = lean_box(0);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4010_);
v___x_4012_ = v___x_4007_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
else
{
lean_object* v___x_4014_; 
lean_del_object(v___x_4007_);
lean_inc_ref(v_arg_3988_);
v___x_4014_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3988_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
v___x_4016_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__3, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3);
v___x_4017_ = l_Lean_mkApp3(v___x_4016_, v_arg_3991_, v_arg_3988_, v_a_4015_);
v___x_4018_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3971_, v___x_4017_, v_a_3972_, v_a_3974_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4018_;
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4019_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4014_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4014_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4028_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4004_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4004_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v___x_4036_; 
lean_inc_ref(v_arg_3991_);
v___x_4036_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_3991_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__5, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5);
v___x_4039_ = l_Lean_mkApp3(v___x_4038_, v_arg_3991_, v_arg_3988_, v_a_4037_);
v___x_4040_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_3971_, v___x_4039_, v_a_3972_, v_a_3974_, v_a_3976_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4040_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4041_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4036_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4036_);
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
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4049_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4001_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4001_);
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
else
{
lean_object* v___x_4057_; 
lean_inc_ref(v_arg_3988_);
v___x_4057_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3988_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; lean_object* v___x_4062_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v___x_4059_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__7, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7);
lean_inc_ref(v_arg_3991_);
v___x_4060_ = l_Lean_mkApp3(v___x_4059_, v_arg_3991_, v_arg_3988_, v_a_4058_);
v___x_4061_ = lean_unbox(v_a_3996_);
lean_dec(v_a_3996_);
v___x_4062_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3971_, v_arg_3991_, v___x_4060_, v___x_4061_, v_a_3972_, v_a_3974_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4062_;
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_3996_);
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4063_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4057_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4057_);
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
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_a_3996_);
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4071_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_3998_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_3998_);
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
else
{
lean_object* v___x_4079_; 
lean_dec(v_a_3996_);
lean_inc_ref(v_arg_3991_);
v___x_4079_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_3991_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__9, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9);
lean_inc_ref(v_arg_3988_);
v___x_4082_ = l_Lean_mkApp3(v___x_4081_, v_arg_3991_, v_arg_3988_, v_a_4080_);
v___x_4083_ = 0;
v___x_4084_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3971_, v_arg_3988_, v___x_4082_, v___x_4083_, v_a_3972_, v_a_3974_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4084_;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4085_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4079_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4079_);
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
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec_ref(v_arg_3991_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3971_);
v_a_4093_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_3995_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_3995_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
v___jp_3983_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object* v_e_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Meta_Grind_propagateBoolAndUp(v_e_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
lean_dec(v_a_4111_);
lean_dec_ref(v_a_4110_);
lean_dec(v_a_4109_);
lean_dec_ref(v_a_4108_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec(v_a_4102_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4116_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp___boxed), 12, 0);
v___x_4117_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4115_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8____boxed(lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_8_();
return v_res_4119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_box(0);
v___x_4126_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__0));
v___x_4127_ = l_Lean_mkConst(v___x_4126_, v___x_4125_);
return v___x_4127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__2));
v___x_4135_ = l_Lean_mkConst(v___x_4134_, v___x_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* v_e_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v___x_4151_; 
lean_inc_ref(v_e_4136_);
v___x_4151_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4136_, v_a_4137_, v_a_4141_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4186_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4186_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4186_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
uint8_t v___x_4156_; 
v___x_4156_ = lean_unbox(v_a_4152_);
lean_dec(v_a_4152_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
lean_dec_ref(v_e_4136_);
v___x_4157_ = lean_box(0);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4157_);
v___x_4159_ = v___x_4154_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
else
{
lean_object* v___x_4161_; uint8_t v___x_4162_; 
lean_del_object(v___x_4154_);
lean_inc_ref(v_e_4136_);
v___x_4161_ = l_Lean_Expr_cleanupAnnotations(v_e_4136_);
v___x_4162_ = l_Lean_Expr_isApp(v___x_4161_);
if (v___x_4162_ == 0)
{
lean_dec_ref(v___x_4161_);
lean_dec_ref(v_e_4136_);
goto v___jp_4148_;
}
else
{
lean_object* v_arg_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v_arg_4163_ = lean_ctor_get(v___x_4161_, 1);
lean_inc_ref(v_arg_4163_);
v___x_4164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4161_);
v___x_4165_ = l_Lean_Expr_isApp(v___x_4164_);
if (v___x_4165_ == 0)
{
lean_dec_ref(v___x_4164_);
lean_dec_ref(v_arg_4163_);
lean_dec_ref(v_e_4136_);
goto v___jp_4148_;
}
else
{
lean_object* v_arg_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
v_arg_4166_ = lean_ctor_get(v___x_4164_, 1);
lean_inc_ref(v_arg_4166_);
v___x_4167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4164_);
v___x_4168_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4169_ = l_Lean_Expr_isConstOf(v___x_4167_, v___x_4168_);
lean_dec_ref(v___x_4167_);
if (v___x_4169_ == 0)
{
lean_dec_ref(v_arg_4166_);
lean_dec_ref(v_arg_4163_);
lean_dec_ref(v_e_4136_);
goto v___jp_4148_;
}
else
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc_n(v_a_4171_, 2);
lean_dec_ref_known(v___x_4170_, 1);
v___x_4172_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__1, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1);
lean_inc_ref(v_arg_4163_);
lean_inc_ref_n(v_arg_4166_, 2);
v___x_4173_ = l_Lean_mkApp3(v___x_4172_, v_arg_4166_, v_arg_4163_, v_a_4171_);
v___x_4174_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4166_, v___x_4173_, v_a_4137_, v_a_4139_, v_a_4141_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_dec_ref_known(v___x_4174_, 1);
v___x_4175_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__3, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3);
lean_inc_ref(v_arg_4163_);
v___x_4176_ = l_Lean_mkApp3(v___x_4175_, v_arg_4166_, v_arg_4163_, v_a_4171_);
v___x_4177_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4163_, v___x_4176_, v_a_4137_, v_a_4139_, v_a_4141_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
return v___x_4177_;
}
else
{
lean_dec(v_a_4171_);
lean_dec_ref(v_arg_4166_);
lean_dec_ref(v_arg_4163_);
return v___x_4174_;
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v_arg_4166_);
lean_dec_ref(v_arg_4163_);
v_a_4178_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4170_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4170_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
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
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v_e_4136_);
v_a_4187_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4151_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4151_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
v___jp_4148_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object* v_e_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_Grind_propagateBoolAndDown(v_e_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec(v_a_4196_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4210_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown___boxed), 12, 0);
v___x_4211_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4209_, v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8____boxed(lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_8_();
return v_res_4213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_box(0);
v___x_4224_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__2));
v___x_4225_ = l_Lean_mkConst(v___x_4224_, v___x_4223_);
return v___x_4225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4231_ = lean_box(0);
v___x_4232_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__4));
v___x_4233_ = l_Lean_mkConst(v___x_4232_, v___x_4231_);
return v___x_4233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = lean_box(0);
v___x_4240_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__6));
v___x_4241_ = l_Lean_mkConst(v___x_4240_, v___x_4239_);
return v___x_4241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9(void){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = lean_box(0);
v___x_4248_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__8));
v___x_4249_ = l_Lean_mkConst(v___x_4248_, v___x_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* v_e_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; 
lean_inc_ref(v_e_4250_);
v___x_4265_ = l_Lean_Expr_cleanupAnnotations(v_e_4250_);
v___x_4266_ = l_Lean_Expr_isApp(v___x_4265_);
if (v___x_4266_ == 0)
{
lean_dec_ref(v___x_4265_);
lean_dec_ref(v_e_4250_);
goto v___jp_4262_;
}
else
{
lean_object* v_arg_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_arg_4267_ = lean_ctor_get(v___x_4265_, 1);
lean_inc_ref(v_arg_4267_);
v___x_4268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4265_);
v___x_4269_ = l_Lean_Expr_isApp(v___x_4268_);
if (v___x_4269_ == 0)
{
lean_dec_ref(v___x_4268_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
goto v___jp_4262_;
}
else
{
lean_object* v_arg_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v_arg_4270_ = lean_ctor_get(v___x_4268_, 1);
lean_inc_ref(v_arg_4270_);
v___x_4271_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4268_);
v___x_4272_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4273_ = l_Lean_Expr_isConstOf(v___x_4271_, v___x_4272_);
lean_dec_ref(v___x_4271_);
if (v___x_4273_ == 0)
{
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
goto v___jp_4262_;
}
else
{
lean_object* v___x_4274_; 
lean_inc_ref(v_arg_4270_);
v___x_4274_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4270_, v_a_4251_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; uint8_t v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v___x_4276_ = lean_unbox(v_a_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
lean_inc_ref(v_arg_4267_);
v___x_4277_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4267_, v_a_4251_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; uint8_t v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v___x_4279_ = lean_unbox(v_a_4278_);
lean_dec(v_a_4278_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; 
lean_dec(v_a_4275_);
lean_inc_ref(v_arg_4270_);
v___x_4280_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4270_, v_a_4251_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; uint8_t v___x_4282_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = lean_unbox(v_a_4281_);
lean_dec(v_a_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; 
lean_inc_ref(v_arg_4267_);
v___x_4283_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4267_, v_a_4251_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4306_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4286_ = v___x_4283_;
v_isShared_4287_ = v_isSharedCheck_4306_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4283_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4306_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_unbox(v_a_4284_);
lean_dec(v_a_4284_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; lean_object* v___x_4291_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v___x_4289_ = lean_box(0);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v___x_4289_);
v___x_4291_ = v___x_4286_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4289_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
else
{
lean_object* v___x_4293_; 
lean_del_object(v___x_4286_);
lean_inc_ref(v_arg_4267_);
v___x_4293_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4267_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
v___x_4295_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__3, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3);
v___x_4296_ = l_Lean_mkApp3(v___x_4295_, v_arg_4270_, v_arg_4267_, v_a_4294_);
v___x_4297_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4250_, v___x_4296_, v_a_4251_, v_a_4253_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
return v___x_4297_;
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4298_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4293_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4293_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4307_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4283_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4283_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v___x_4315_; 
lean_inc_ref(v_arg_4270_);
v___x_4315_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4270_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__5, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5);
v___x_4318_ = l_Lean_mkApp3(v___x_4317_, v_arg_4270_, v_arg_4267_, v_a_4316_);
v___x_4319_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4250_, v___x_4318_, v_a_4251_, v_a_4253_, v_a_4255_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
return v___x_4319_;
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4320_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4315_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4315_);
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
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4328_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4280_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4280_);
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
else
{
lean_object* v___x_4336_; 
lean_inc_ref(v_arg_4267_);
v___x_4336_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4267_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__7, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7);
lean_inc_ref(v_arg_4270_);
v___x_4339_ = l_Lean_mkApp3(v___x_4338_, v_arg_4270_, v_arg_4267_, v_a_4337_);
v___x_4340_ = lean_unbox(v_a_4275_);
lean_dec(v_a_4275_);
v___x_4341_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4250_, v_arg_4270_, v___x_4339_, v___x_4340_, v_a_4251_, v_a_4253_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
return v___x_4341_;
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_dec(v_a_4275_);
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4342_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4336_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4336_);
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
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
lean_dec(v_a_4275_);
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4350_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4277_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4277_);
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
else
{
lean_object* v___x_4358_; 
lean_dec(v_a_4275_);
lean_inc_ref(v_arg_4270_);
v___x_4358_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4270_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; lean_object* v___x_4363_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__9, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9);
lean_inc_ref(v_arg_4267_);
v___x_4361_ = l_Lean_mkApp3(v___x_4360_, v_arg_4270_, v_arg_4267_, v_a_4359_);
v___x_4362_ = 0;
v___x_4363_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4250_, v_arg_4267_, v___x_4361_, v___x_4362_, v_a_4251_, v_a_4253_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
return v___x_4363_;
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4364_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4358_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4358_);
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
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec_ref(v_arg_4270_);
lean_dec_ref(v_arg_4267_);
lean_dec_ref(v_e_4250_);
v_a_4372_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4274_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4274_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
}
v___jp_4262_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = lean_box(0);
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object* v_e_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_Meta_Grind_propagateBoolOrUp(v_e_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec(v_a_4381_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4394_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4395_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp___boxed), 12, 0);
v___x_4396_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4394_, v___x_4395_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8____boxed(lean_object* v_a_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_8_();
return v_res_4398_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__0));
v___x_4406_ = l_Lean_mkConst(v___x_4405_, v___x_4404_);
return v___x_4406_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4412_ = lean_box(0);
v___x_4413_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__2));
v___x_4414_ = l_Lean_mkConst(v___x_4413_, v___x_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* v_e_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4430_; 
lean_inc_ref(v_e_4415_);
v___x_4430_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4415_, v_a_4416_, v_a_4420_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4465_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4465_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4465_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
uint8_t v___x_4435_; 
v___x_4435_ = lean_unbox(v_a_4431_);
lean_dec(v_a_4431_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
lean_dec_ref(v_e_4415_);
v___x_4436_ = lean_box(0);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4436_);
v___x_4438_ = v___x_4433_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
else
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
lean_del_object(v___x_4433_);
lean_inc_ref(v_e_4415_);
v___x_4440_ = l_Lean_Expr_cleanupAnnotations(v_e_4415_);
v___x_4441_ = l_Lean_Expr_isApp(v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec_ref(v___x_4440_);
lean_dec_ref(v_e_4415_);
goto v___jp_4427_;
}
else
{
lean_object* v_arg_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v_arg_4442_ = lean_ctor_get(v___x_4440_, 1);
lean_inc_ref(v_arg_4442_);
v___x_4443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4440_);
v___x_4444_ = l_Lean_Expr_isApp(v___x_4443_);
if (v___x_4444_ == 0)
{
lean_dec_ref(v___x_4443_);
lean_dec_ref(v_arg_4442_);
lean_dec_ref(v_e_4415_);
goto v___jp_4427_;
}
else
{
lean_object* v_arg_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v_arg_4445_ = lean_ctor_get(v___x_4443_, 1);
lean_inc_ref(v_arg_4445_);
v___x_4446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4443_);
v___x_4447_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4448_ = l_Lean_Expr_isConstOf(v___x_4446_, v___x_4447_);
lean_dec_ref(v___x_4446_);
if (v___x_4448_ == 0)
{
lean_dec_ref(v_arg_4445_);
lean_dec_ref(v_arg_4442_);
lean_dec_ref(v_e_4415_);
goto v___jp_4427_;
}
else
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_n(v_a_4450_, 2);
lean_dec_ref_known(v___x_4449_, 1);
v___x_4451_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__1, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1);
lean_inc_ref(v_arg_4442_);
lean_inc_ref_n(v_arg_4445_, 2);
v___x_4452_ = l_Lean_mkApp3(v___x_4451_, v_arg_4445_, v_arg_4442_, v_a_4450_);
v___x_4453_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4445_, v___x_4452_, v_a_4416_, v_a_4418_, v_a_4420_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
lean_dec_ref_known(v___x_4453_, 1);
v___x_4454_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__3, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3);
lean_inc_ref(v_arg_4442_);
v___x_4455_ = l_Lean_mkApp3(v___x_4454_, v_arg_4445_, v_arg_4442_, v_a_4450_);
v___x_4456_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4442_, v___x_4455_, v_a_4416_, v_a_4418_, v_a_4420_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
return v___x_4456_;
}
else
{
lean_dec(v_a_4450_);
lean_dec_ref(v_arg_4445_);
lean_dec_ref(v_arg_4442_);
return v___x_4453_;
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec_ref(v_arg_4445_);
lean_dec_ref(v_arg_4442_);
v_a_4457_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4449_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4449_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
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
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_dec_ref(v_e_4415_);
v_a_4466_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4430_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4430_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
v___jp_4427_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = lean_box(0);
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object* v_e_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_Meta_Grind_propagateBoolOrDown(v_e_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
lean_dec(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec(v_a_4475_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4489_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown___boxed), 12, 0);
v___x_4490_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4488_, v___x_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8____boxed(lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_8_();
return v_res_4492_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3(void){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = lean_box(0);
v___x_4503_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__2));
v___x_4504_ = l_Lean_mkConst(v___x_4503_, v___x_4502_);
return v___x_4504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5(void){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_box(0);
v___x_4511_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__4));
v___x_4512_ = l_Lean_mkConst(v___x_4511_, v___x_4510_);
return v___x_4512_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7(void){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4518_ = lean_box(0);
v___x_4519_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__6));
v___x_4520_ = l_Lean_mkConst(v___x_4519_, v___x_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* v_e_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v___x_4536_; uint8_t v___x_4537_; 
lean_inc_ref(v_e_4521_);
v___x_4536_ = l_Lean_Expr_cleanupAnnotations(v_e_4521_);
v___x_4537_ = l_Lean_Expr_isApp(v___x_4536_);
if (v___x_4537_ == 0)
{
lean_dec_ref(v___x_4536_);
lean_dec_ref(v_e_4521_);
goto v___jp_4533_;
}
else
{
lean_object* v_arg_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v_arg_4538_ = lean_ctor_get(v___x_4536_, 1);
lean_inc_ref(v_arg_4538_);
v___x_4539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4536_);
v___x_4540_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4541_ = l_Lean_Expr_isConstOf(v___x_4539_, v___x_4540_);
lean_dec_ref(v___x_4539_);
if (v___x_4541_ == 0)
{
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
goto v___jp_4533_;
}
else
{
lean_object* v___x_4542_; 
lean_inc_ref(v_arg_4538_);
v___x_4542_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4538_, v_a_4522_, v_a_4526_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; uint8_t v___x_4544_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4542_, 1);
v___x_4544_ = lean_unbox(v_a_4543_);
lean_dec(v_a_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; 
lean_inc_ref(v_arg_4538_);
v___x_4545_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4538_, v_a_4522_, v_a_4526_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; uint8_t v___x_4547_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v___x_4547_ = lean_unbox(v_a_4546_);
lean_dec(v_a_4546_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4521_, v_arg_4538_, v_a_4522_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4571_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4571_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4571_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
uint8_t v___x_4553_; 
v___x_4553_ = lean_unbox(v_a_4549_);
lean_dec(v_a_4549_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4556_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v___x_4554_ = lean_box(0);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4554_);
v___x_4556_ = v___x_4551_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
else
{
lean_object* v___x_4558_; 
lean_del_object(v___x_4551_);
lean_inc(v_a_4531_);
lean_inc_ref(v_a_4530_);
lean_inc(v_a_4529_);
lean_inc_ref(v_a_4528_);
lean_inc(v_a_4527_);
lean_inc_ref(v_a_4526_);
lean_inc(v_a_4525_);
lean_inc_ref(v_a_4524_);
lean_inc(v_a_4523_);
lean_inc(v_a_4522_);
lean_inc_ref(v_arg_4538_);
v___x_4558_ = lean_grind_mk_eq_proof(v_e_4521_, v_arg_4538_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4560_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4561_ = l_Lean_mkAppB(v___x_4560_, v_arg_4538_, v_a_4559_);
v___x_4562_ = l_Lean_Meta_Grind_closeGoal(v___x_4561_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
return v___x_4562_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v_arg_4538_);
v_a_4563_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4558_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4558_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v_a_4572_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4548_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4548_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v___x_4580_; 
lean_inc_ref(v_arg_4538_);
v___x_4580_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4538_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4580_, 1);
v___x_4582_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__5, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5);
v___x_4583_ = l_Lean_mkAppB(v___x_4582_, v_arg_4538_, v_a_4581_);
v___x_4584_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4521_, v___x_4583_, v_a_4522_, v_a_4524_, v_a_4526_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
return v___x_4584_;
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v_a_4585_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4580_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4580_);
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
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v_a_4593_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4545_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4545_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v___x_4601_; 
lean_inc_ref(v_arg_4538_);
v___x_4601_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4538_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__7, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7);
v___x_4604_ = l_Lean_mkAppB(v___x_4603_, v_arg_4538_, v_a_4602_);
v___x_4605_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4521_, v___x_4604_, v_a_4522_, v_a_4524_, v_a_4526_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
return v___x_4605_;
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v_a_4606_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4601_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4601_);
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
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_dec_ref(v_arg_4538_);
lean_dec_ref(v_e_4521_);
v_a_4614_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4542_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4542_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
v___jp_4533_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = lean_box(0);
v___x_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
return v___x_4535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object* v_e_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_Meta_Grind_propagateBoolNotUp(v_e_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec(v_a_4623_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4637_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp___boxed), 12, 0);
v___x_4638_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4636_, v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8____boxed(lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_8_();
return v_res_4640_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = lean_box(0);
v___x_4647_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__0));
v___x_4648_ = l_Lean_mkConst(v___x_4647_, v___x_4646_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4654_ = lean_box(0);
v___x_4655_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__2));
v___x_4656_ = l_Lean_mkConst(v___x_4655_, v___x_4654_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* v_e_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v___x_4672_; uint8_t v___x_4673_; 
lean_inc_ref(v_e_4657_);
v___x_4672_ = l_Lean_Expr_cleanupAnnotations(v_e_4657_);
v___x_4673_ = l_Lean_Expr_isApp(v___x_4672_);
if (v___x_4673_ == 0)
{
lean_dec_ref(v___x_4672_);
lean_dec_ref(v_e_4657_);
goto v___jp_4669_;
}
else
{
lean_object* v_arg_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; uint8_t v___x_4677_; 
v_arg_4674_ = lean_ctor_get(v___x_4672_, 1);
lean_inc_ref(v_arg_4674_);
v___x_4675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4672_);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4677_ = l_Lean_Expr_isConstOf(v___x_4675_, v___x_4676_);
lean_dec_ref(v___x_4675_);
if (v___x_4677_ == 0)
{
lean_dec_ref(v_arg_4674_);
lean_dec_ref(v_e_4657_);
goto v___jp_4669_;
}
else
{
lean_object* v___x_4678_; 
lean_inc_ref(v_e_4657_);
v___x_4678_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4657_, v_a_4658_, v_a_4662_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; uint8_t v___x_4680_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v___x_4680_ = lean_unbox(v_a_4679_);
lean_dec(v_a_4679_);
if (v___x_4680_ == 0)
{
lean_object* v___x_4681_; 
lean_inc_ref(v_e_4657_);
v___x_4681_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4657_, v_a_4658_, v_a_4662_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; uint8_t v___x_4683_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v___x_4683_ = lean_unbox(v_a_4682_);
lean_dec(v_a_4682_);
if (v___x_4683_ == 0)
{
lean_object* v___x_4684_; 
v___x_4684_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4657_, v_arg_4674_, v_a_4658_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4707_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4687_ = v___x_4684_;
v_isShared_4688_ = v_isSharedCheck_4707_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4684_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4707_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
uint8_t v___x_4689_; 
v___x_4689_ = lean_unbox(v_a_4685_);
lean_dec(v_a_4685_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4692_; 
lean_dec_ref(v_arg_4674_);
lean_dec_ref(v_e_4657_);
v___x_4690_ = lean_box(0);
if (v_isShared_4688_ == 0)
{
lean_ctor_set(v___x_4687_, 0, v___x_4690_);
v___x_4692_ = v___x_4687_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
else
{
lean_object* v___x_4694_; 
lean_del_object(v___x_4687_);
lean_inc(v_a_4667_);
lean_inc_ref(v_a_4666_);
lean_inc(v_a_4665_);
lean_inc_ref(v_a_4664_);
lean_inc(v_a_4663_);
lean_inc_ref(v_a_4662_);
lean_inc(v_a_4661_);
lean_inc_ref(v_a_4660_);
lean_inc(v_a_4659_);
lean_inc(v_a_4658_);
lean_inc_ref(v_arg_4674_);
v___x_4694_ = lean_grind_mk_eq_proof(v_e_4657_, v_arg_4674_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4694_, 1);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4697_ = l_Lean_mkAppB(v___x_4696_, v_arg_4674_, v_a_4695_);
v___x_4698_ = l_Lean_Meta_Grind_closeGoal(v___x_4697_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4698_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec_ref(v_arg_4674_);
v_a_4699_ = lean_ctor_get(v___x_4694_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4694_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4694_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4694_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
lean_dec_ref(v_arg_4674_);
lean_dec_ref(v_e_4657_);
v_a_4708_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4684_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4684_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
else
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v___x_4718_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__1, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1);
lean_inc_ref(v_arg_4674_);
v___x_4719_ = l_Lean_mkAppB(v___x_4718_, v_arg_4674_, v_a_4717_);
v___x_4720_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4674_, v___x_4719_, v_a_4658_, v_a_4660_, v_a_4662_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4720_;
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec_ref(v_arg_4674_);
v_a_4721_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4716_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4716_);
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
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec_ref(v_arg_4674_);
lean_dec_ref(v_e_4657_);
v_a_4729_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4681_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4681_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
else
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4739_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__3, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3);
lean_inc_ref(v_arg_4674_);
v___x_4740_ = l_Lean_mkAppB(v___x_4739_, v_arg_4674_, v_a_4738_);
v___x_4741_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4674_, v___x_4740_, v_a_4658_, v_a_4660_, v_a_4662_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4741_;
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec_ref(v_arg_4674_);
v_a_4742_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4737_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4737_);
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
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec_ref(v_arg_4674_);
lean_dec_ref(v_e_4657_);
v_a_4750_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4678_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4678_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
v___jp_4669_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = lean_box(0);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
return v___x_4671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object* v_e_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_Meta_Grind_propagateBoolNotDown(v_e_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
lean_dec(v_a_4762_);
lean_dec_ref(v_a_4761_);
lean_dec(v_a_4760_);
lean_dec(v_a_4759_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4772_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown___boxed), 12, 0);
v___x_4774_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4772_, v___x_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8____boxed(lean_object* v_a_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_8_();
return v_res_4776_;
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
