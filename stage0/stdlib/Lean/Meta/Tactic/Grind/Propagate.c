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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_propagateAndUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_38_ = stack[0].m_obj;
lean_object* v_a_39_ = stack[1].m_obj;
lean_object* v_a_40_ = stack[2].m_obj;
lean_object* v_a_41_ = stack[3].m_obj;
lean_object* v_a_42_ = stack[4].m_obj;
lean_object* v_a_43_ = stack[5].m_obj;
lean_object* v_a_44_ = stack[6].m_obj;
lean_object* v_a_45_ = stack[7].m_obj;
lean_object* v_a_46_ = stack[8].m_obj;
lean_object* v_a_47_ = stack[9].m_obj;
lean_object* v_a_48_ = stack[10].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Meta_Grind_propagateAndUp(v_e_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp___boxed(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_Grind_propagateAndUp(v_e_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec(v_a_170_);
return v_res_181_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_184_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndUp___boxed), 12, 0);
v___x_185_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_186_;
v_res_186_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_();
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9____boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndUp___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2341738659____hygCtx___hyg_9_();
return v_res_188_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__2(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__1));
v___x_196_ = l_Lean_mkConst(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateAndDown___closed__5(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_box(0);
v___x_203_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndDown___closed__4));
v___x_204_ = l_Lean_mkConst(v___x_203_, v___x_202_);
return v___x_204_;
}
}
lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object* v_e_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_220_; 
lean_inc_ref(v_e_205_);
v___x_220_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_205_, v_a_206_, v_a_210_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_255_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_255_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_255_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_255_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_unbox(v_a_221_);
lean_dec(v_a_221_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_228_; 
lean_dec_ref(v_e_205_);
v___x_226_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
lean_del_object(v___x_223_);
lean_inc_ref(v_e_205_);
v___x_230_ = l_Lean_Expr_cleanupAnnotations(v_e_205_);
v___x_231_ = l_Lean_Expr_isApp(v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v___x_230_);
lean_dec_ref(v_e_205_);
goto v___jp_217_;
}
else
{
lean_object* v_arg_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_arg_232_ = lean_ctor_get(v___x_230_, 1);
lean_inc_ref(v_arg_232_);
v___x_233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_230_);
v___x_234_ = l_Lean_Expr_isApp(v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v___x_233_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_e_205_);
goto v___jp_217_;
}
else
{
lean_object* v_arg_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_arg_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc_ref(v_arg_235_);
v___x_236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_233_);
v___x_237_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_238_ = l_Lean_Expr_isConstOf(v___x_236_, v___x_237_);
lean_dec_ref(v___x_236_);
if (v___x_238_ == 0)
{
lean_dec_ref(v_arg_235_);
lean_dec_ref(v_arg_232_);
lean_dec_ref(v_e_205_);
goto v___jp_217_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_n(v_a_240_, 2);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndDown___closed__2, &l_Lean_Meta_Grind_propagateAndDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateAndDown___closed__2);
lean_inc_ref(v_arg_232_);
lean_inc_ref_n(v_arg_235_, 2);
v___x_242_ = l_Lean_mkApp3(v___x_241_, v_arg_235_, v_arg_232_, v_a_240_);
v___x_243_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_235_, v___x_242_, v_a_206_, v_a_208_, v_a_210_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_243_, 1);
v___x_244_ = lean_obj_once(&l_Lean_Meta_Grind_propagateAndDown___closed__5, &l_Lean_Meta_Grind_propagateAndDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateAndDown___closed__5);
lean_inc_ref(v_arg_232_);
v___x_245_ = l_Lean_mkApp3(v___x_244_, v_arg_235_, v_arg_232_, v_a_240_);
v___x_246_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_232_, v___x_245_, v_a_206_, v_a_208_, v_a_210_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
return v___x_246_;
}
else
{
lean_dec(v_a_240_);
lean_dec_ref(v_arg_235_);
lean_dec_ref(v_arg_232_);
return v___x_243_;
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v_arg_235_);
lean_dec_ref(v_arg_232_);
v_a_247_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_239_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_239_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
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
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_e_205_);
v_a_256_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_220_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_220_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_box(0);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateAndDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_205_ = stack[0].m_obj;
lean_object* v_a_206_ = stack[1].m_obj;
lean_object* v_a_207_ = stack[2].m_obj;
lean_object* v_a_208_ = stack[3].m_obj;
lean_object* v_a_209_ = stack[4].m_obj;
lean_object* v_a_210_ = stack[5].m_obj;
lean_object* v_a_211_ = stack[6].m_obj;
lean_object* v_a_212_ = stack[7].m_obj;
lean_object* v_a_213_ = stack[8].m_obj;
lean_object* v_a_214_ = stack[9].m_obj;
lean_object* v_a_215_ = stack[10].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lean_Meta_Grind_propagateAndDown(v_e_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_Grind_propagateAndDown(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec(v_a_266_);
return v_res_277_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__1));
v___x_280_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndDown___boxed), 12, 0);
v___x_281_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_282_;
v_res_282_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_();
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9____boxed(lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateAndDown___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_976872719____hygCtx___hyg_9_();
return v_res_284_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__4(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_box(0);
v___x_294_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__3));
v___x_295_ = l_Lean_mkConst(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__7(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_box(0);
v___x_302_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__6));
v___x_303_ = l_Lean_mkConst(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__10(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__9));
v___x_311_ = l_Lean_mkConst(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrUp___closed__13(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
v___x_318_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__12));
v___x_319_ = l_Lean_mkConst(v___x_318_, v___x_317_);
return v___x_319_;
}
}
lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object* v_e_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
lean_inc_ref(v_e_320_);
v___x_335_ = l_Lean_Expr_cleanupAnnotations(v_e_320_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_e_320_);
goto v___jp_332_;
}
else
{
lean_object* v_arg_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_arg_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc_ref(v_arg_337_);
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_339_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
goto v___jp_332_;
}
else
{
lean_object* v_arg_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_arg_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc_ref(v_arg_340_);
v___x_341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_342_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_341_, v___x_342_);
lean_dec_ref(v___x_341_);
if (v___x_343_ == 0)
{
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
goto v___jp_332_;
}
else
{
lean_object* v___x_344_; 
lean_inc_ref(v_arg_340_);
v___x_344_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_340_, v_a_321_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = lean_unbox(v_a_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_inc_ref(v_arg_337_);
v___x_347_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_337_, v_a_321_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; uint8_t v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec(v_a_345_);
lean_inc_ref(v_arg_340_);
v___x_350_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_340_, v_a_321_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; uint8_t v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_inc_ref(v_arg_337_);
v___x_353_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_337_, v_a_321_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_376_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_376_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_376_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_376_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_unbox(v_a_354_);
lean_dec(v_a_354_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_361_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v___x_359_ = lean_box(0);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_359_);
v___x_361_ = v___x_356_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_363_; 
lean_del_object(v___x_356_);
lean_inc_ref(v_arg_337_);
v___x_363_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_337_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__4, &l_Lean_Meta_Grind_propagateOrUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__4);
v___x_366_ = l_Lean_mkApp3(v___x_365_, v_arg_340_, v_arg_337_, v_a_364_);
v___x_367_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_320_, v___x_366_, v_a_321_, v_a_323_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_367_;
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_368_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_363_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_363_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_377_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_353_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_353_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v___x_385_; 
lean_inc_ref(v_arg_340_);
v___x_385_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_340_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__7, &l_Lean_Meta_Grind_propagateOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__7);
v___x_388_ = l_Lean_mkApp3(v___x_387_, v_arg_340_, v_arg_337_, v_a_386_);
v___x_389_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_320_, v___x_388_, v_a_321_, v_a_323_, v_a_325_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_389_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_390_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_385_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_385_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_398_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_350_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_350_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v___x_406_; 
lean_inc_ref(v_arg_337_);
v___x_406_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_337_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__10, &l_Lean_Meta_Grind_propagateOrUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__10);
lean_inc_ref(v_arg_340_);
v___x_409_ = l_Lean_mkApp3(v___x_408_, v_arg_340_, v_arg_337_, v_a_407_);
v___x_410_ = lean_unbox(v_a_345_);
lean_dec(v_a_345_);
v___x_411_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_320_, v_arg_340_, v___x_409_, v___x_410_, v_a_321_, v_a_323_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_411_;
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_345_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_412_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_406_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_406_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_a_345_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_420_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_347_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_347_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v___x_428_; 
lean_dec(v_a_345_);
lean_inc_ref(v_arg_340_);
v___x_428_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_340_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrUp___closed__13, &l_Lean_Meta_Grind_propagateOrUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateOrUp___closed__13);
lean_inc_ref(v_arg_337_);
v___x_431_ = l_Lean_mkApp3(v___x_430_, v_arg_340_, v_arg_337_, v_a_429_);
v___x_432_ = 0;
v___x_433_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_320_, v_arg_337_, v___x_431_, v___x_432_, v_a_321_, v_a_323_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_433_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_434_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_428_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_428_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
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
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_337_);
lean_dec_ref(v_e_320_);
v_a_442_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_344_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_344_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
v___jp_332_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateOrUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_320_ = stack[0].m_obj;
lean_object* v_a_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_a_323_ = stack[3].m_obj;
lean_object* v_a_324_ = stack[4].m_obj;
lean_object* v_a_325_ = stack[5].m_obj;
lean_object* v_a_326_ = stack[6].m_obj;
lean_object* v_a_327_ = stack[7].m_obj;
lean_object* v_a_328_ = stack[8].m_obj;
lean_object* v_a_329_ = stack[9].m_obj;
lean_object* v_a_330_ = stack[10].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_Meta_Grind_propagateOrUp(v_e_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp___boxed(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_propagateOrUp(v_e_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
return v_res_463_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_466_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrUp___boxed), 12, 0);
v___x_467_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_468_;
v_res_468_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_();
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9____boxed(lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrUp___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3848872352____hygCtx___hyg_9_();
return v_res_470_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__2(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__1));
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateOrDown___closed__5(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_box(0);
v___x_485_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrDown___closed__4));
v___x_486_ = l_Lean_mkConst(v___x_485_, v___x_484_);
return v___x_486_;
}
}
lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object* v_e_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_502_; 
lean_inc_ref(v_e_487_);
v___x_502_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_487_, v_a_488_, v_a_492_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_537_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_537_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_537_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_537_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v___x_507_; 
v___x_507_ = lean_unbox(v_a_503_);
lean_dec(v_a_503_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec_ref(v_e_487_);
v___x_508_ = lean_box(0);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
lean_del_object(v___x_505_);
lean_inc_ref(v_e_487_);
v___x_512_ = l_Lean_Expr_cleanupAnnotations(v_e_487_);
v___x_513_ = l_Lean_Expr_isApp(v___x_512_);
if (v___x_513_ == 0)
{
lean_dec_ref(v___x_512_);
lean_dec_ref(v_e_487_);
goto v___jp_499_;
}
else
{
lean_object* v_arg_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_arg_514_ = lean_ctor_get(v___x_512_, 1);
lean_inc_ref(v_arg_514_);
v___x_515_ = l_Lean_Expr_appFnCleanup___redArg(v___x_512_);
v___x_516_ = l_Lean_Expr_isApp(v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v___x_515_);
lean_dec_ref(v_arg_514_);
lean_dec_ref(v_e_487_);
goto v___jp_499_;
}
else
{
lean_object* v_arg_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_arg_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc_ref(v_arg_517_);
v___x_518_ = l_Lean_Expr_appFnCleanup___redArg(v___x_515_);
v___x_519_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_520_ = l_Lean_Expr_isConstOf(v___x_518_, v___x_519_);
lean_dec_ref(v___x_518_);
if (v___x_520_ == 0)
{
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_arg_514_);
lean_dec_ref(v_e_487_);
goto v___jp_499_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_n(v_a_522_, 2);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrDown___closed__2, &l_Lean_Meta_Grind_propagateOrDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateOrDown___closed__2);
lean_inc_ref(v_arg_514_);
lean_inc_ref_n(v_arg_517_, 2);
v___x_524_ = l_Lean_mkApp3(v___x_523_, v_arg_517_, v_arg_514_, v_a_522_);
v___x_525_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_517_, v___x_524_, v_a_488_, v_a_490_, v_a_492_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref_known(v___x_525_, 1);
v___x_526_ = lean_obj_once(&l_Lean_Meta_Grind_propagateOrDown___closed__5, &l_Lean_Meta_Grind_propagateOrDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateOrDown___closed__5);
lean_inc_ref(v_arg_514_);
v___x_527_ = l_Lean_mkApp3(v___x_526_, v_arg_517_, v_arg_514_, v_a_522_);
v___x_528_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_514_, v___x_527_, v_a_488_, v_a_490_, v_a_492_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_528_;
}
else
{
lean_dec(v_a_522_);
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_arg_514_);
return v___x_525_;
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_arg_517_);
lean_dec_ref(v_arg_514_);
v_a_529_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_521_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_521_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
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
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_e_487_);
v_a_538_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_502_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_502_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateOrDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_487_ = stack[0].m_obj;
lean_object* v_a_488_ = stack[1].m_obj;
lean_object* v_a_489_ = stack[2].m_obj;
lean_object* v_a_490_ = stack[3].m_obj;
lean_object* v_a_491_ = stack[4].m_obj;
lean_object* v_a_492_ = stack[5].m_obj;
lean_object* v_a_493_ = stack[6].m_obj;
lean_object* v_a_494_ = stack[7].m_obj;
lean_object* v_a_495_ = stack[8].m_obj;
lean_object* v_a_496_ = stack[9].m_obj;
lean_object* v_a_497_ = stack[10].m_obj;
lean_object* v_res_546_;
v_res_546_ = l_Lean_Meta_Grind_propagateOrDown(v_e_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown___boxed(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_Grind_propagateOrDown(v_e_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
return v_res_559_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_propagateOrUp___closed__1));
v___x_562_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrDown___boxed), 12, 0);
v___x_563_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_561_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_564_;
v_res_564_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_();
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9____boxed(lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateOrDown___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2934405114____hygCtx___hyg_9_();
return v_res_566_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__4(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__3));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__7(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__6));
v___x_585_ = l_Lean_mkConst(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotUp___closed__10(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_box(0);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__9));
v___x_593_ = l_Lean_mkConst(v___x_592_, v___x_591_);
return v___x_593_;
}
}
lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object* v_e_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_609_; uint8_t v___x_610_; 
lean_inc_ref(v_e_594_);
v___x_609_ = l_Lean_Expr_cleanupAnnotations(v_e_594_);
v___x_610_ = l_Lean_Expr_isApp(v___x_609_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___x_609_);
lean_dec_ref(v_e_594_);
goto v___jp_606_;
}
else
{
lean_object* v_arg_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_arg_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc_ref(v_arg_611_);
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_609_);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_614_ = l_Lean_Expr_isConstOf(v___x_612_, v___x_613_);
lean_dec_ref(v___x_612_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
goto v___jp_606_;
}
else
{
lean_object* v___x_615_; 
lean_inc_ref(v_arg_611_);
v___x_615_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_611_, v_a_595_, v_a_599_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_inc_ref(v_arg_611_);
v___x_618_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_611_, v_a_595_, v_a_599_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; uint8_t v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_594_, v_arg_611_, v_a_595_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_644_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_644_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_644_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; 
v___x_626_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_629_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v___x_627_ = lean_box(0);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_631_; 
lean_del_object(v___x_624_);
lean_inc(v_a_604_);
lean_inc_ref(v_a_603_);
lean_inc(v_a_602_);
lean_inc_ref(v_a_601_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
lean_inc(v_a_596_);
lean_inc(v_a_595_);
lean_inc_ref(v_arg_611_);
v___x_631_ = lean_grind_mk_eq_proof(v_e_594_, v_arg_611_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__4, &l_Lean_Meta_Grind_propagateNotUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__4);
v___x_634_ = l_Lean_mkAppB(v___x_633_, v_arg_611_, v_a_632_);
v___x_635_ = l_Lean_Meta_Grind_closeGoal(v___x_634_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_635_;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_arg_611_);
v_a_636_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_631_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_631_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
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
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v_a_645_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_621_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_621_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; 
lean_inc_ref(v_arg_611_);
v___x_653_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_611_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__7, &l_Lean_Meta_Grind_propagateNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__7);
v___x_656_ = l_Lean_mkAppB(v___x_655_, v_arg_611_, v_a_654_);
v___x_657_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_594_, v___x_656_, v_a_595_, v_a_597_, v_a_599_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v_a_658_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_653_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_653_);
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
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v_a_666_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_618_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_618_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v___x_674_; 
lean_inc_ref(v_arg_611_);
v___x_674_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_611_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__10, &l_Lean_Meta_Grind_propagateNotUp___closed__10_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__10);
v___x_677_ = l_Lean_mkAppB(v___x_676_, v_arg_611_, v_a_675_);
v___x_678_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_594_, v___x_677_, v_a_595_, v_a_597_, v_a_599_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_678_;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v_a_679_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_674_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_674_);
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
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_arg_611_);
lean_dec_ref(v_e_594_);
v_a_687_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_615_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_615_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
v___jp_606_:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateNotUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_594_ = stack[0].m_obj;
lean_object* v_a_595_ = stack[1].m_obj;
lean_object* v_a_596_ = stack[2].m_obj;
lean_object* v_a_597_ = stack[3].m_obj;
lean_object* v_a_598_ = stack[4].m_obj;
lean_object* v_a_599_ = stack[5].m_obj;
lean_object* v_a_600_ = stack[6].m_obj;
lean_object* v_a_601_ = stack[7].m_obj;
lean_object* v_a_602_ = stack[8].m_obj;
lean_object* v_a_603_ = stack[9].m_obj;
lean_object* v_a_604_ = stack[10].m_obj;
lean_object* v_res_695_;
v_res_695_ = l_Lean_Meta_Grind_propagateNotUp(v_e_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp___boxed(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_Grind_propagateNotUp(v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec(v_a_697_);
return v_res_708_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_711_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotUp___boxed), 12, 0);
v___x_712_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_713_;
v_res_713_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_();
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9____boxed(lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotUp___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4175663102____hygCtx___hyg_9_();
return v_res_715_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__2(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_box(0);
v___x_722_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__1));
v___x_723_ = l_Lean_mkConst(v___x_722_, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNotDown___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotDown___closed__4));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_729_);
return v___x_731_;
}
}
lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
lean_inc_ref(v_e_732_);
v___x_747_ = l_Lean_Expr_cleanupAnnotations(v_e_732_);
v___x_748_ = l_Lean_Expr_isApp(v___x_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v___x_747_);
lean_dec_ref(v_e_732_);
goto v___jp_744_;
}
else
{
lean_object* v_arg_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_arg_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc_ref(v_arg_749_);
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_747_);
v___x_751_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_752_ = l_Lean_Expr_isConstOf(v___x_750_, v___x_751_);
lean_dec_ref(v___x_750_);
if (v___x_752_ == 0)
{
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_e_732_);
goto v___jp_744_;
}
else
{
lean_object* v___x_753_; 
lean_inc_ref(v_e_732_);
v___x_753_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_732_, v_a_733_, v_a_737_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; uint8_t v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = lean_unbox(v_a_754_);
lean_dec(v_a_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_inc_ref(v_e_732_);
v___x_756_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_732_, v_a_733_, v_a_737_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; uint8_t v___x_758_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = lean_unbox(v_a_757_);
lean_dec(v_a_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_732_, v_arg_749_, v_a_733_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_782_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_782_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_782_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_782_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = lean_unbox(v_a_760_);
lean_dec(v_a_760_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_e_732_);
v___x_765_ = lean_box(0);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_769_; 
lean_del_object(v___x_762_);
lean_inc(v_a_742_);
lean_inc_ref(v_a_741_);
lean_inc(v_a_740_);
lean_inc_ref(v_a_739_);
lean_inc(v_a_738_);
lean_inc_ref(v_a_737_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_arg_749_);
v___x_769_ = lean_grind_mk_eq_proof(v_e_732_, v_arg_749_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotUp___closed__4, &l_Lean_Meta_Grind_propagateNotUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateNotUp___closed__4);
v___x_772_ = l_Lean_mkAppB(v___x_771_, v_arg_749_, v_a_770_);
v___x_773_ = l_Lean_Meta_Grind_closeGoal(v___x_772_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_773_;
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_arg_749_);
v_a_774_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_769_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_769_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_e_732_);
v_a_783_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_759_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_759_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotDown___closed__2, &l_Lean_Meta_Grind_propagateNotDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateNotDown___closed__2);
lean_inc_ref(v_arg_749_);
v___x_794_ = l_Lean_mkAppB(v___x_793_, v_arg_749_, v_a_792_);
v___x_795_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_749_, v___x_794_, v_a_733_, v_a_735_, v_a_737_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_795_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_arg_749_);
v_a_796_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_791_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_791_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_e_732_);
v_a_804_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_756_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_756_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
v___x_814_ = lean_obj_once(&l_Lean_Meta_Grind_propagateNotDown___closed__5, &l_Lean_Meta_Grind_propagateNotDown___closed__5_once, _init_l_Lean_Meta_Grind_propagateNotDown___closed__5);
lean_inc_ref(v_arg_749_);
v___x_815_ = l_Lean_mkAppB(v___x_814_, v_arg_749_, v_a_813_);
v___x_816_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_749_, v___x_815_, v_a_733_, v_a_735_, v_a_737_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_816_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_arg_749_);
v_a_817_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_812_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_812_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_arg_749_);
lean_dec_ref(v_e_732_);
v_a_825_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_753_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_753_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
v___jp_744_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateNotDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_732_ = stack[0].m_obj;
lean_object* v_a_733_ = stack[1].m_obj;
lean_object* v_a_734_ = stack[2].m_obj;
lean_object* v_a_735_ = stack[3].m_obj;
lean_object* v_a_736_ = stack[4].m_obj;
lean_object* v_a_737_ = stack[5].m_obj;
lean_object* v_a_738_ = stack[6].m_obj;
lean_object* v_a_739_ = stack[7].m_obj;
lean_object* v_a_740_ = stack[8].m_obj;
lean_object* v_a_741_ = stack[9].m_obj;
lean_object* v_a_742_ = stack[10].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lean_Meta_Grind_propagateNotDown(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown___boxed(lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Grind_propagateNotDown(v_e_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec(v_a_835_);
return v_res_846_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = ((lean_object*)(l_Lean_Meta_Grind_propagateNotUp___closed__1));
v___x_849_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotDown___boxed), 12, 0);
v___x_850_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_848_, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_851_;
v_res_851_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_();
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9____boxed(lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateNotDown___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3610191934____hygCtx___hyg_9_();
return v_res_853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__2));
v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = lean_box(0);
v___x_871_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__5));
v___x_872_ = l_Lean_mkConst(v___x_871_, v___x_870_);
return v___x_872_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object* v_eq_873_, lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_880_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_880_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_875_, v_a_890_, v_a_876_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; uint8_t v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_unbox(v_a_892_);
lean_dec(v_a_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_isEqv___redArg(v_b_875_, v_a_888_, v_a_876_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; uint8_t v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = lean_unbox(v_a_895_);
lean_dec(v_a_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_874_, v_a_890_, v_a_876_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; uint8_t v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_unbox(v_a_898_);
lean_dec(v_a_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_a_890_);
v___x_900_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_874_, v_a_888_, v_a_876_);
lean_dec_ref(v_a_874_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_923_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_923_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint8_t v___x_905_; 
v___x_905_ = lean_unbox(v_a_901_);
lean_dec(v_a_901_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_908_; 
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_eq_873_);
v___x_906_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_906_);
v___x_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_910_; 
lean_del_object(v___x_903_);
lean_inc_ref(v_b_875_);
v___x_910_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_b_875_, v_a_888_, v_eq_873_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__3, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3);
lean_inc_ref(v_b_875_);
v___x_913_ = l_Lean_mkAppB(v___x_912_, v_b_875_, v_a_911_);
v___x_914_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_b_875_, v___x_913_, v_a_876_, v_a_878_, v_a_880_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_b_875_);
v_a_915_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_910_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_eq_873_);
v_a_924_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_900_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_900_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
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
else
{
lean_object* v___x_932_; 
lean_dec(v_a_888_);
lean_dec_ref(v_a_874_);
lean_inc_ref(v_b_875_);
v___x_932_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_b_875_, v_a_890_, v_eq_873_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__6, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__6_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6);
lean_inc_ref(v_b_875_);
v___x_935_ = l_Lean_mkAppB(v___x_934_, v_b_875_, v_a_933_);
v___x_936_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_b_875_, v___x_935_, v_a_876_, v_a_878_, v_a_880_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_936_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_b_875_);
v_a_937_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_932_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_890_);
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_eq_873_);
v_a_945_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_897_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_897_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_a_890_);
lean_dec_ref(v_b_875_);
lean_inc_ref(v_a_874_);
v___x_953_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_874_, v_a_888_, v_eq_873_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__3, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__3);
lean_inc_ref(v_a_874_);
v___x_956_ = l_Lean_mkAppB(v___x_955_, v_a_874_, v_a_954_);
v___x_957_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_a_874_, v___x_956_, v_a_876_, v_a_878_, v_a_880_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_957_;
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_a_874_);
v_a_958_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_953_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_953_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_890_);
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_eq_873_);
v_a_966_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_894_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_894_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_974_; 
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_inc_ref(v_a_874_);
v___x_974_ = l_Lean_Meta_Grind_mkDiseqProofUsing(v_a_874_, v_a_890_, v_eq_873_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolDiseq___closed__6, &l_Lean_Meta_Grind_propagateBoolDiseq___closed__6_once, _init_l_Lean_Meta_Grind_propagateBoolDiseq___closed__6);
lean_inc_ref(v_a_874_);
v___x_977_ = l_Lean_mkAppB(v___x_976_, v_a_874_, v_a_975_);
v___x_978_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_a_874_, v___x_977_, v_a_876_, v_a_878_, v_a_880_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v___x_978_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v_a_874_);
v_a_979_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_974_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_974_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v_a_890_);
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_eq_873_);
v_a_987_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_891_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_891_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_a_888_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_eq_873_);
v_a_995_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_889_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_889_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_b_875_);
lean_dec_ref(v_a_874_);
lean_dec_ref(v_eq_873_);
v_a_1003_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_887_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_887_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_873_ = stack[0].m_obj;
lean_object* v_a_874_ = stack[1].m_obj;
lean_object* v_b_875_ = stack[2].m_obj;
lean_object* v_a_876_ = stack[3].m_obj;
lean_object* v_a_877_ = stack[4].m_obj;
lean_object* v_a_878_ = stack[5].m_obj;
lean_object* v_a_879_ = stack[6].m_obj;
lean_object* v_a_880_ = stack[7].m_obj;
lean_object* v_a_881_ = stack[8].m_obj;
lean_object* v_a_882_ = stack[9].m_obj;
lean_object* v_a_883_ = stack[10].m_obj;
lean_object* v_a_884_ = stack[11].m_obj;
lean_object* v_a_885_ = stack[12].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_eq_873_, v_a_874_, v_b_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq___boxed(lean_object* v_eq_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_eq_1012_, v_a_1013_, v_b_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec(v_a_1015_);
return v_res_1026_;
}
}
lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(uint8_t v_a_1027_, uint8_t v___x_1028_, lean_object* v_self_1029_, lean_object* v_arg_1030_, lean_object* v_arg_1031_, lean_object* v_self_1032_, lean_object* v_hab_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_hf_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___x_1074_; 
lean_inc_ref(v_self_1029_);
lean_inc_ref(v_arg_1030_);
v___x_1074_ = l_Lean_Meta_Grind_hasSameType(v_arg_1030_, v_self_1029_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
lean_inc_ref(v_self_1032_);
lean_inc_ref(v_arg_1031_);
v___x_1076_ = l_Lean_Meta_Grind_hasSameType(v_arg_1031_, v_self_1032_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1076_) == 0)
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_unbox(v_a_1075_);
lean_dec(v_a_1075_);
if (v___x_1077_ == 1)
{
lean_object* v_a_1078_; uint8_t v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1079_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1079_ == 1)
{
lean_object* v___x_1080_; 
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1080_ = lean_grind_mk_eq_proof(v_self_1029_, v_arg_1030_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
lean_inc_ref(v_hab_1033_);
v___x_1082_ = l_Lean_Meta_mkEqTrans(v_a_1081_, v_hab_1033_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1084_ = lean_grind_mk_eq_proof(v_arg_1031_, v_self_1032_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_Meta_mkEqTrans(v_a_1083_, v_a_1085_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v_hf_1046_ = v_a_1087_;
v___y_1047_ = v___y_1038_;
v___y_1048_ = v___y_1040_;
v___y_1049_ = v___y_1041_;
v___y_1050_ = v___y_1042_;
v___y_1051_ = v___y_1043_;
goto v___jp_1045_;
}
else
{
lean_dec_ref(v_hab_1033_);
return v___x_1086_;
}
}
else
{
lean_dec(v_a_1083_);
lean_dec_ref(v_hab_1033_);
return v___x_1084_;
}
}
else
{
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
return v___x_1082_;
}
}
else
{
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
return v___x_1080_;
}
}
else
{
goto v___jp_1061_;
}
}
else
{
lean_dec_ref_known(v___x_1076_, 1);
goto v___jp_1061_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1075_);
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_self_1029_);
v_a_1088_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1076_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1076_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1030_);
lean_dec_ref(v_self_1029_);
v_a_1096_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1074_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1074_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
v___jp_1045_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1047_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1054_ = l_Lean_Meta_mkNoConfusion(v_a_1053_, v_hf_1046_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_mk_empty_array_with_capacity(v___x_1056_);
v___x_1058_ = lean_array_push(v___x_1057_, v_hab_1033_);
v___x_1059_ = 1;
v___x_1060_ = l_Lean_Meta_mkLambdaFVars(v___x_1058_, v_a_1055_, v_a_1027_, v___x_1028_, v_a_1027_, v___x_1028_, v___x_1059_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec_ref(v___x_1058_);
return v___x_1060_;
}
else
{
lean_dec_ref(v_hab_1033_);
return v___x_1054_;
}
}
else
{
lean_dec_ref(v_hf_1046_);
lean_dec_ref(v_hab_1033_);
return v___x_1052_;
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; 
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1062_ = lean_grind_mk_heq_proof(v_self_1029_, v_arg_1030_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
lean_inc_ref(v_hab_1033_);
v___x_1064_ = l_Lean_Meta_mkHEqOfEq(v_hab_1033_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l_Lean_Meta_mkHEqTrans(v_a_1063_, v_a_1065_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc(v___y_1034_);
v___x_1068_ = lean_grind_mk_heq_proof(v_arg_1031_, v_self_1032_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_Meta_mkHEqTrans(v_a_1067_, v_a_1069_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = l_Lean_Meta_mkEqOfHEq(v_a_1071_, v___x_1028_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v_hf_1046_ = v_a_1073_;
v___y_1047_ = v___y_1038_;
v___y_1048_ = v___y_1040_;
v___y_1049_ = v___y_1041_;
v___y_1050_ = v___y_1042_;
v___y_1051_ = v___y_1043_;
goto v___jp_1045_;
}
else
{
lean_dec_ref(v_hab_1033_);
return v___x_1072_;
}
}
else
{
lean_dec_ref(v_hab_1033_);
return v___x_1070_;
}
}
else
{
lean_dec(v_a_1067_);
lean_dec_ref(v_hab_1033_);
return v___x_1068_;
}
}
else
{
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
return v___x_1066_;
}
}
else
{
lean_dec(v_a_1063_);
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
return v___x_1064_;
}
}
else
{
lean_dec_ref(v_hab_1033_);
lean_dec_ref(v_self_1032_);
lean_dec_ref(v_arg_1031_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateEqUp___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1027_ = stack[0].m_num;
uint8_t v___x_1028_ = stack[1].m_num;
lean_object* v_self_1029_ = stack[2].m_obj;
lean_object* v_arg_1030_ = stack[3].m_obj;
lean_object* v_arg_1031_ = stack[4].m_obj;
lean_object* v_self_1032_ = stack[5].m_obj;
lean_object* v_hab_1033_ = stack[6].m_obj;
lean_object* v___y_1034_ = stack[7].m_obj;
lean_object* v___y_1035_ = stack[8].m_obj;
lean_object* v___y_1036_ = stack[9].m_obj;
lean_object* v___y_1037_ = stack[10].m_obj;
lean_object* v___y_1038_ = stack[11].m_obj;
lean_object* v___y_1039_ = stack[12].m_obj;
lean_object* v___y_1040_ = stack[13].m_obj;
lean_object* v___y_1041_ = stack[14].m_obj;
lean_object* v___y_1042_ = stack[15].m_obj;
lean_object* v___y_1043_ = stack[16].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_Meta_Grind_propagateEqUp___lam__0(v_a_1027_, v___x_1028_, v_self_1029_, v_arg_1030_, v_arg_1031_, v_self_1032_, v_hab_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object** _args){
lean_object* v_a_1105_ = _args[0];
lean_object* v___x_1106_ = _args[1];
lean_object* v_self_1107_ = _args[2];
lean_object* v_arg_1108_ = _args[3];
lean_object* v_arg_1109_ = _args[4];
lean_object* v_self_1110_ = _args[5];
lean_object* v_hab_1111_ = _args[6];
lean_object* v___y_1112_ = _args[7];
lean_object* v___y_1113_ = _args[8];
lean_object* v___y_1114_ = _args[9];
lean_object* v___y_1115_ = _args[10];
lean_object* v___y_1116_ = _args[11];
lean_object* v___y_1117_ = _args[12];
lean_object* v___y_1118_ = _args[13];
lean_object* v___y_1119_ = _args[14];
lean_object* v___y_1120_ = _args[15];
lean_object* v___y_1121_ = _args[16];
lean_object* v___y_1122_ = _args[17];
_start:
{
uint8_t v_a_111361__boxed_1123_; uint8_t v___x_111362__boxed_1124_; lean_object* v_res_1125_; 
v_a_111361__boxed_1123_ = lean_unbox(v_a_1105_);
v___x_111362__boxed_1124_ = lean_unbox(v___x_1106_);
v_res_1125_ = l_Lean_Meta_Grind_propagateEqUp___lam__0(v_a_111361__boxed_1123_, v___x_111362__boxed_1124_, v_self_1107_, v_arg_1108_, v_arg_1109_, v_self_1110_, v_hab_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
return v_res_1125_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v___y_1128_);
lean_inc(v___y_1127_);
v___x_1139_ = lean_apply_12(v_k_1126_, v_b_1133_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
return v___x_1139_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1126_ = stack[0].m_obj;
lean_object* v___y_1127_ = stack[1].m_obj;
lean_object* v___y_1128_ = stack[2].m_obj;
lean_object* v___y_1129_ = stack[3].m_obj;
lean_object* v___y_1130_ = stack[4].m_obj;
lean_object* v___y_1131_ = stack[5].m_obj;
lean_object* v___y_1132_ = stack[6].m_obj;
lean_object* v_b_1133_ = stack[7].m_obj;
lean_object* v___y_1134_ = stack[8].m_obj;
lean_object* v___y_1135_ = stack[9].m_obj;
lean_object* v___y_1136_ = stack[10].m_obj;
lean_object* v___y_1137_ = stack[11].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(v_k_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v_b_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0(v_k_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
return v_res_1154_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(lean_object* v_name_1155_, uint8_t v_bi_1156_, lean_object* v_type_1157_, lean_object* v_k_1158_, uint8_t v_kind_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v___y_1161_);
lean_inc(v___y_1160_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_1171_, 0, v_k_1158_);
lean_closure_set(v___f_1171_, 1, v___y_1160_);
lean_closure_set(v___f_1171_, 2, v___y_1161_);
lean_closure_set(v___f_1171_, 3, v___y_1162_);
lean_closure_set(v___f_1171_, 4, v___y_1163_);
lean_closure_set(v___f_1171_, 5, v___y_1164_);
lean_closure_set(v___f_1171_, 6, v___y_1165_);
v___x_1172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1155_, v_bi_1156_, v_type_1157_, v___f_1171_, v_kind_1159_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1172_) == 0)
{
return v___x_1172_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1155_ = stack[0].m_obj;
uint8_t v_bi_1156_ = stack[1].m_num;
lean_object* v_type_1157_ = stack[2].m_obj;
lean_object* v_k_1158_ = stack[3].m_obj;
uint8_t v_kind_1159_ = stack[4].m_num;
lean_object* v___y_1160_ = stack[5].m_obj;
lean_object* v___y_1161_ = stack[6].m_obj;
lean_object* v___y_1162_ = stack[7].m_obj;
lean_object* v___y_1163_ = stack[8].m_obj;
lean_object* v___y_1164_ = stack[9].m_obj;
lean_object* v___y_1165_ = stack[10].m_obj;
lean_object* v___y_1166_ = stack[11].m_obj;
lean_object* v___y_1167_ = stack[12].m_obj;
lean_object* v___y_1168_ = stack[13].m_obj;
lean_object* v___y_1169_ = stack[14].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1155_, v_bi_1156_, v_type_1157_, v_k_1158_, v_kind_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg___boxed(lean_object* v_name_1182_, lean_object* v_bi_1183_, lean_object* v_type_1184_, lean_object* v_k_1185_, lean_object* v_kind_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_bi_boxed_1198_; uint8_t v_kind_boxed_1199_; lean_object* v_res_1200_; 
v_bi_boxed_1198_ = lean_unbox(v_bi_1183_);
v_kind_boxed_1199_ = lean_unbox(v_kind_1186_);
v_res_1200_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1182_, v_bi_boxed_1198_, v_type_1184_, v_k_1185_, v_kind_boxed_1199_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1200_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(lean_object* v_name_1201_, lean_object* v_type_1202_, lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = 0;
v___x_1216_ = 0;
v___x_1217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_1201_, v___x_1215_, v_type_1202_, v_k_1203_, v___x_1216_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1201_ = stack[0].m_obj;
lean_object* v_type_1202_ = stack[1].m_obj;
lean_object* v_k_1203_ = stack[2].m_obj;
lean_object* v___y_1204_ = stack[3].m_obj;
lean_object* v___y_1205_ = stack[4].m_obj;
lean_object* v___y_1206_ = stack[5].m_obj;
lean_object* v___y_1207_ = stack[6].m_obj;
lean_object* v___y_1208_ = stack[7].m_obj;
lean_object* v___y_1209_ = stack[8].m_obj;
lean_object* v___y_1210_ = stack[9].m_obj;
lean_object* v___y_1211_ = stack[10].m_obj;
lean_object* v___y_1212_ = stack[11].m_obj;
lean_object* v___y_1213_ = stack[12].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_1201_, v_type_1202_, v_k_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg___boxed(lean_object* v_name_1219_, lean_object* v_type_1220_, lean_object* v_k_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_1219_, v_type_1220_, v_k_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
return v_res_1233_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(uint8_t v_a_1234_, uint8_t v___x_1235_, lean_object* v_self_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_self_1239_, lean_object* v_hab_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_hf_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___x_1281_; 
lean_inc_ref(v_self_1236_);
lean_inc_ref(v_a_1237_);
v___x_1281_ = l_Lean_Meta_Grind_hasSameType(v_a_1237_, v_self_1236_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
lean_inc_ref(v_self_1239_);
lean_inc_ref(v_a_1238_);
v___x_1283_ = l_Lean_Meta_Grind_hasSameType(v_a_1238_, v_self_1239_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1283_) == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
if (v___x_1284_ == 1)
{
lean_object* v_a_1285_; uint8_t v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1286_ = lean_unbox(v_a_1285_);
lean_dec(v_a_1285_);
if (v___x_1286_ == 1)
{
lean_object* v___x_1287_; 
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc(v___y_1241_);
v___x_1287_ = lean_grind_mk_eq_proof(v_self_1236_, v_a_1237_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
lean_inc_ref(v_hab_1240_);
v___x_1289_ = l_Lean_Meta_mkEqTrans(v_a_1288_, v_hab_1240_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc(v___y_1241_);
v___x_1291_ = lean_grind_mk_eq_proof(v_a_1238_, v_self_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = l_Lean_Meta_mkEqTrans(v_a_1290_, v_a_1292_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v_hf_1253_ = v_a_1294_;
v___y_1254_ = v___y_1245_;
v___y_1255_ = v___y_1247_;
v___y_1256_ = v___y_1248_;
v___y_1257_ = v___y_1249_;
v___y_1258_ = v___y_1250_;
goto v___jp_1252_;
}
else
{
lean_dec_ref(v_hab_1240_);
return v___x_1293_;
}
}
else
{
lean_dec(v_a_1290_);
lean_dec_ref(v_hab_1240_);
return v___x_1291_;
}
}
else
{
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
return v___x_1289_;
}
}
else
{
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
return v___x_1287_;
}
}
else
{
goto v___jp_1268_;
}
}
else
{
lean_dec_ref_known(v___x_1283_, 1);
goto v___jp_1268_;
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1282_);
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec_ref(v_self_1236_);
v_a_1295_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1283_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1283_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec_ref(v_self_1236_);
v_a_1303_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1281_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1281_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
v___jp_1252_:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_1254_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1261_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = l_Lean_Meta_mkNoConfusion(v_a_1260_, v_hf_1253_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_array_push(v___x_1264_, v_hab_1240_);
v___x_1266_ = 1;
v___x_1267_ = l_Lean_Meta_mkLambdaFVars(v___x_1265_, v_a_1262_, v_a_1234_, v___x_1235_, v_a_1234_, v___x_1235_, v___x_1266_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec_ref(v___x_1265_);
return v___x_1267_;
}
else
{
lean_dec_ref(v_hab_1240_);
return v___x_1261_;
}
}
else
{
lean_dec_ref(v_hf_1253_);
lean_dec_ref(v_hab_1240_);
return v___x_1259_;
}
}
v___jp_1268_:
{
lean_object* v___x_1269_; 
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc(v___y_1241_);
v___x_1269_ = lean_grind_mk_heq_proof(v_self_1236_, v_a_1237_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
lean_inc_ref(v_hab_1240_);
v___x_1271_ = l_Lean_Meta_mkHEqOfEq(v_hab_1240_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = l_Lean_Meta_mkHEqTrans(v_a_1270_, v_a_1272_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1275_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1273_, 1);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc(v___y_1241_);
v___x_1275_ = lean_grind_mk_heq_proof(v_a_1238_, v_self_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Lean_Meta_mkHEqTrans(v_a_1274_, v_a_1276_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_Lean_Meta_mkEqOfHEq(v_a_1278_, v___x_1235_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v_hf_1253_ = v_a_1280_;
v___y_1254_ = v___y_1245_;
v___y_1255_ = v___y_1247_;
v___y_1256_ = v___y_1248_;
v___y_1257_ = v___y_1249_;
v___y_1258_ = v___y_1250_;
goto v___jp_1252_;
}
else
{
lean_dec_ref(v_hab_1240_);
return v___x_1279_;
}
}
else
{
lean_dec_ref(v_hab_1240_);
return v___x_1277_;
}
}
else
{
lean_dec(v_a_1274_);
lean_dec_ref(v_hab_1240_);
return v___x_1275_;
}
}
else
{
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
return v___x_1273_;
}
}
else
{
lean_dec(v_a_1270_);
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
return v___x_1271_;
}
}
else
{
lean_dec_ref(v_hab_1240_);
lean_dec_ref(v_self_1239_);
lean_dec_ref(v_a_1238_);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1234_ = stack[0].m_num;
uint8_t v___x_1235_ = stack[1].m_num;
lean_object* v_self_1236_ = stack[2].m_obj;
lean_object* v_a_1237_ = stack[3].m_obj;
lean_object* v_a_1238_ = stack[4].m_obj;
lean_object* v_self_1239_ = stack[5].m_obj;
lean_object* v_hab_1240_ = stack[6].m_obj;
lean_object* v___y_1241_ = stack[7].m_obj;
lean_object* v___y_1242_ = stack[8].m_obj;
lean_object* v___y_1243_ = stack[9].m_obj;
lean_object* v___y_1244_ = stack[10].m_obj;
lean_object* v___y_1245_ = stack[11].m_obj;
lean_object* v___y_1246_ = stack[12].m_obj;
lean_object* v___y_1247_ = stack[13].m_obj;
lean_object* v___y_1248_ = stack[14].m_obj;
lean_object* v___y_1249_ = stack[15].m_obj;
lean_object* v___y_1250_ = stack[16].m_obj;
lean_object* v_res_1311_;
v_res_1311_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(v_a_1234_, v___x_1235_, v_self_1236_, v_a_1237_, v_a_1238_, v_self_1239_, v_hab_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
stack->m_obj
 = v_res_1311_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1312_ = _args[0];
lean_object* v___x_1313_ = _args[1];
lean_object* v_self_1314_ = _args[2];
lean_object* v_a_1315_ = _args[3];
lean_object* v_a_1316_ = _args[4];
lean_object* v_self_1317_ = _args[5];
lean_object* v_hab_1318_ = _args[6];
lean_object* v___y_1319_ = _args[7];
lean_object* v___y_1320_ = _args[8];
lean_object* v___y_1321_ = _args[9];
lean_object* v___y_1322_ = _args[10];
lean_object* v___y_1323_ = _args[11];
lean_object* v___y_1324_ = _args[12];
lean_object* v___y_1325_ = _args[13];
lean_object* v___y_1326_ = _args[14];
lean_object* v___y_1327_ = _args[15];
lean_object* v___y_1328_ = _args[16];
lean_object* v___y_1329_ = _args[17];
_start:
{
uint8_t v_a_111830__boxed_1330_; uint8_t v___x_111831__boxed_1331_; lean_object* v_res_1332_; 
v_a_111830__boxed_1330_ = lean_unbox(v_a_1312_);
v___x_111831__boxed_1331_ = lean_unbox(v___x_1313_);
v_res_1332_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0(v_a_111830__boxed_1330_, v___x_111831__boxed_1331_, v_self_1314_, v_a_1315_, v_a_1316_, v_self_1317_, v_hab_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
return v_res_1332_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__1));
v___x_1338_ = l_Lean_mkConst(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_e_1344_, uint8_t v___x_1345_, uint8_t v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1451_; 
v_snd_1360_ = lean_ctor_get(v_a_1348_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_a_1348_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v_a_1348_, 0);
lean_dec(v_unused_1452_);
v___x_1362_ = v_a_1348_;
v_isShared_1363_ = v_isSharedCheck_1451_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_dec(v_a_1348_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1451_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_st_ref_get(v___y_1349_);
lean_inc(v_snd_1360_);
v___x_1366_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1365_, v_snd_1360_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1442_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1442_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1442_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_self_1371_; lean_object* v_next_1372_; uint8_t v_ctor_1373_; uint8_t v_a_1389_; lean_object* v___y_1395_; lean_object* v___y_1417_; 
v_self_1371_ = lean_ctor_get(v_a_1367_, 0);
lean_inc_ref(v_self_1371_);
v_next_1372_ = lean_ctor_get(v_a_1367_, 1);
lean_inc_ref(v_next_1372_);
v_ctor_1373_ = lean_ctor_get_uint8(v_a_1367_, sizeof(void*)*12 + 2);
lean_dec(v_a_1367_);
if (v_ctor_1373_ == 0)
{
lean_dec_ref(v_self_1371_);
goto v___jp_1374_;
}
else
{
lean_object* v_self_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_self_1428_ = lean_ctor_get(v_a_1343_, 0);
v___x_1429_ = l_Lean_Expr_getAppFn(v_self_1428_);
v___x_1430_ = l_Lean_Expr_getAppFn(v_self_1371_);
v___x_1431_ = lean_expr_eqv(v___x_1429_, v___x_1430_);
lean_dec_ref(v___x_1430_);
lean_dec_ref(v___x_1429_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; 
v___x_1432_ = lean_box(v_a_1346_);
v___x_1433_ = lean_box(v___x_1345_);
lean_inc_ref(v_self_1371_);
lean_inc_ref(v_a_1342_);
lean_inc_ref(v_a_1347_);
lean_inc_ref_n(v_self_1428_, 2);
v___f_1434_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1434_, 0, v___x_1432_);
lean_closure_set(v___f_1434_, 1, v___x_1433_);
lean_closure_set(v___f_1434_, 2, v_self_1428_);
lean_closure_set(v___f_1434_, 3, v_a_1347_);
lean_closure_set(v___f_1434_, 4, v_a_1342_);
lean_closure_set(v___f_1434_, 5, v_self_1371_);
v___x_1435_ = l_Lean_Meta_Grind_hasSameType(v_self_1428_, v_self_1371_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; uint8_t v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v___x_1437_ = lean_unbox(v_a_1436_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v___f_1434_);
v___y_1417_ = v___x_1435_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1438_; 
lean_dec_ref_known(v___x_1435_, 1);
lean_inc_ref(v_a_1342_);
lean_inc_ref(v_a_1347_);
v___x_1438_ = l_Lean_Meta_mkEq(v_a_1347_, v_a_1342_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1441_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1440_, v_a_1439_, v___f_1434_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
v___y_1395_ = v___x_1441_;
goto v___jp_1394_;
}
else
{
lean_dec_ref(v___f_1434_);
v___y_1395_ = v___x_1438_;
goto v___jp_1394_;
}
}
}
else
{
lean_dec_ref(v___f_1434_);
v___y_1417_ = v___x_1435_;
goto v___jp_1416_;
}
}
else
{
lean_dec_ref(v_self_1371_);
goto v___jp_1374_;
}
}
v___jp_1374_:
{
size_t v___x_1375_; size_t v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = lean_ptr_addr(v_next_1372_);
v___x_1376_ = lean_ptr_addr(v_a_1342_);
v___x_1377_ = lean_usize_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1379_; 
lean_del_object(v___x_1369_);
lean_dec(v_snd_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v_next_1372_);
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1379_ = v___x_1362_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_next_1372_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_a_1348_ = v___x_1379_;
goto _start;
}
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v_next_1372_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1383_ = v___x_1362_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1360_);
v___x_1383_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1383_);
v___x_1385_ = v___x_1369_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1388_:
{
if (v_a_1389_ == 0)
{
goto v___jp_1374_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_next_1372_);
lean_del_object(v___x_1369_);
lean_del_object(v___x_1362_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
v___x_1390_ = lean_box(v_a_1389_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v_snd_1360_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
v___jp_1394_:
{
if (lean_obj_tag(v___y_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___y_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___y_1395_, 1);
v___x_1397_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref_n(v_e_1344_, 2);
v___x_1398_ = l_Lean_mkAppB(v___x_1397_, v_e_1344_, v_a_1396_);
v___x_1399_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1344_, v___x_1398_, v___y_1349_, v___y_1351_, v___y_1353_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_dec_ref_known(v___x_1399_, 1);
v_a_1389_ = v___x_1345_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_next_1372_);
lean_del_object(v___x_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_next_1372_);
lean_del_object(v___x_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
v_a_1408_ = lean_ctor_get(v___y_1395_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___y_1395_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___y_1395_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___y_1395_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
v___jp_1416_:
{
if (lean_obj_tag(v___y_1417_) == 0)
{
lean_object* v_a_1418_; uint8_t v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___y_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___y_1417_, 1);
v___x_1419_ = lean_unbox(v_a_1418_);
lean_dec(v_a_1418_);
v_a_1389_ = v___x_1419_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v_next_1372_);
lean_del_object(v___x_1369_);
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
v_a_1420_ = lean_ctor_get(v___y_1417_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___y_1417_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___y_1417_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___y_1417_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_del_object(v___x_1362_);
lean_dec(v_snd_1360_);
lean_dec_ref(v_a_1347_);
lean_dec_ref(v_e_1344_);
lean_dec_ref(v_a_1343_);
lean_dec_ref(v_a_1342_);
v_a_1443_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1366_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1366_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1342_ = stack[0].m_obj;
lean_object* v_a_1343_ = stack[1].m_obj;
lean_object* v_e_1344_ = stack[2].m_obj;
uint8_t v___x_1345_ = stack[3].m_num;
uint8_t v_a_1346_ = stack[4].m_num;
lean_object* v_a_1347_ = stack[5].m_obj;
lean_object* v_a_1348_ = stack[6].m_obj;
lean_object* v___y_1349_ = stack[7].m_obj;
lean_object* v___y_1350_ = stack[8].m_obj;
lean_object* v___y_1351_ = stack[9].m_obj;
lean_object* v___y_1352_ = stack[10].m_obj;
lean_object* v___y_1353_ = stack[11].m_obj;
lean_object* v___y_1354_ = stack[12].m_obj;
lean_object* v___y_1355_ = stack[13].m_obj;
lean_object* v___y_1356_ = stack[14].m_obj;
lean_object* v___y_1357_ = stack[15].m_obj;
lean_object* v___y_1358_ = stack[16].m_obj;
lean_object* v_res_1453_;
v_res_1453_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1342_, v_a_1343_, v_e_1344_, v___x_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1454_ = _args[0];
lean_object* v_a_1455_ = _args[1];
lean_object* v_e_1456_ = _args[2];
lean_object* v___x_1457_ = _args[3];
lean_object* v_a_1458_ = _args[4];
lean_object* v_a_1459_ = _args[5];
lean_object* v_a_1460_ = _args[6];
lean_object* v___y_1461_ = _args[7];
lean_object* v___y_1462_ = _args[8];
lean_object* v___y_1463_ = _args[9];
lean_object* v___y_1464_ = _args[10];
lean_object* v___y_1465_ = _args[11];
lean_object* v___y_1466_ = _args[12];
lean_object* v___y_1467_ = _args[13];
lean_object* v___y_1468_ = _args[14];
lean_object* v___y_1469_ = _args[15];
lean_object* v___y_1470_ = _args[16];
lean_object* v___y_1471_ = _args[17];
_start:
{
uint8_t v___x_112111__boxed_1472_; uint8_t v_a_112112__boxed_1473_; lean_object* v_res_1474_; 
v___x_112111__boxed_1472_ = lean_unbox(v___x_1457_);
v_a_112112__boxed_1473_ = lean_unbox(v_a_1458_);
v_res_1474_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1454_, v_a_1455_, v_e_1456_, v___x_112111__boxed_1472_, v_a_112112__boxed_1473_, v_a_1459_, v_a_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec(v___y_1461_);
return v_res_1474_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(lean_object* v_a_1475_, lean_object* v_a_1476_, uint8_t v_a_1477_, uint8_t v___x_1478_, lean_object* v_a_1479_, lean_object* v_e_1480_, lean_object* v_a_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1584_; 
v_snd_1493_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v_a_1481_, 0);
lean_dec(v_unused_1585_);
v___x_1495_ = v_a_1481_;
v_isShared_1496_ = v_isSharedCheck_1584_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_dec(v_a_1481_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1584_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_st_ref_get(v___y_1482_);
lean_inc(v_snd_1493_);
v___x_1499_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1498_, v_snd_1493_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1575_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1575_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1575_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_self_1504_; lean_object* v_next_1505_; uint8_t v_ctor_1506_; uint8_t v_a_1522_; lean_object* v___y_1528_; lean_object* v___y_1550_; 
v_self_1504_ = lean_ctor_get(v_a_1500_, 0);
lean_inc_ref(v_self_1504_);
v_next_1505_ = lean_ctor_get(v_a_1500_, 1);
lean_inc_ref(v_next_1505_);
v_ctor_1506_ = lean_ctor_get_uint8(v_a_1500_, sizeof(void*)*12 + 2);
lean_dec(v_a_1500_);
if (v_ctor_1506_ == 0)
{
lean_dec_ref(v_self_1504_);
goto v___jp_1507_;
}
else
{
lean_object* v_self_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_self_1561_ = lean_ctor_get(v_a_1476_, 0);
v___x_1562_ = l_Lean_Expr_getAppFn(v_self_1561_);
v___x_1563_ = l_Lean_Expr_getAppFn(v_self_1504_);
v___x_1564_ = lean_expr_eqv(v___x_1562_, v___x_1563_);
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1562_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; 
v___x_1565_ = lean_box(v_a_1477_);
v___x_1566_ = lean_box(v___x_1478_);
lean_inc_ref(v_self_1504_);
lean_inc_ref(v_a_1475_);
lean_inc_ref(v_a_1479_);
lean_inc_ref_n(v_self_1561_, 2);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1567_, 0, v___x_1565_);
lean_closure_set(v___f_1567_, 1, v___x_1566_);
lean_closure_set(v___f_1567_, 2, v_self_1561_);
lean_closure_set(v___f_1567_, 3, v_a_1479_);
lean_closure_set(v___f_1567_, 4, v_a_1475_);
lean_closure_set(v___f_1567_, 5, v_self_1504_);
v___x_1568_ = l_Lean_Meta_Grind_hasSameType(v_self_1561_, v_self_1504_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v___x_1570_ = lean_unbox(v_a_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v___f_1567_);
v___y_1550_ = v___x_1568_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1571_; 
lean_dec_ref_known(v___x_1568_, 1);
lean_inc_ref(v_a_1475_);
lean_inc_ref(v_a_1479_);
v___x_1571_ = l_Lean_Meta_mkEq(v_a_1479_, v_a_1475_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1574_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1573_, v_a_1572_, v___f_1567_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
v___y_1528_ = v___x_1574_;
goto v___jp_1527_;
}
else
{
lean_dec_ref(v___f_1567_);
v___y_1528_ = v___x_1571_;
goto v___jp_1527_;
}
}
}
else
{
lean_dec_ref(v___f_1567_);
v___y_1550_ = v___x_1568_;
goto v___jp_1549_;
}
}
else
{
lean_dec_ref(v_self_1504_);
goto v___jp_1507_;
}
}
v___jp_1507_:
{
size_t v___x_1508_; size_t v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_ptr_addr(v_next_1505_);
v___x_1509_ = lean_ptr_addr(v_a_1475_);
v___x_1510_ = lean_usize_dec_eq(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1512_; 
lean_del_object(v___x_1502_);
lean_dec(v_snd_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_next_1505_);
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1512_ = v___x_1495_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_next_1505_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_1475_, v_a_1476_, v_e_1480_, v___x_1478_, v_a_1477_, v_a_1479_, v___x_1512_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1516_; 
lean_dec_ref(v_next_1505_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1516_ = v___x_1495_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_snd_1493_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1516_);
v___x_1518_ = v___x_1502_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
v___jp_1521_:
{
if (v_a_1522_ == 0)
{
goto v___jp_1507_;
}
else
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v_next_1505_);
lean_del_object(v___x_1502_);
lean_del_object(v___x_1495_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
v___x_1523_ = lean_box(v_a_1522_);
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v_snd_1493_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
v___jp_1527_:
{
if (lean_obj_tag(v___y_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_a_1529_ = lean_ctor_get(v___y_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___y_1528_, 1);
v___x_1530_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref_n(v_e_1480_, 2);
v___x_1531_ = l_Lean_mkAppB(v___x_1530_, v_e_1480_, v_a_1529_);
v___x_1532_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1480_, v___x_1531_, v___y_1482_, v___y_1484_, v___y_1486_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref_known(v___x_1532_, 1);
v_a_1522_ = v___x_1478_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_next_1505_);
lean_del_object(v___x_1502_);
lean_del_object(v___x_1495_);
lean_dec(v_snd_1493_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_next_1505_);
lean_del_object(v___x_1502_);
lean_del_object(v___x_1495_);
lean_dec(v_snd_1493_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
v_a_1541_ = lean_ctor_get(v___y_1528_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___y_1528_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___y_1528_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___y_1528_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
v___jp_1549_:
{
if (lean_obj_tag(v___y_1550_) == 0)
{
lean_object* v_a_1551_; uint8_t v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___y_1550_, 1);
v___x_1552_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
v_a_1522_ = v___x_1552_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_next_1505_);
lean_del_object(v___x_1502_);
lean_del_object(v___x_1495_);
lean_dec(v_snd_1493_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
v_a_1553_ = lean_ctor_get(v___y_1550_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___y_1550_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___y_1550_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___y_1550_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_del_object(v___x_1495_);
lean_dec(v_snd_1493_);
lean_dec_ref(v_e_1480_);
lean_dec_ref(v_a_1479_);
lean_dec_ref(v_a_1476_);
lean_dec_ref(v_a_1475_);
v_a_1576_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1499_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1499_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1475_ = stack[0].m_obj;
lean_object* v_a_1476_ = stack[1].m_obj;
uint8_t v_a_1477_ = stack[2].m_num;
uint8_t v___x_1478_ = stack[3].m_num;
lean_object* v_a_1479_ = stack[4].m_obj;
lean_object* v_e_1480_ = stack[5].m_obj;
lean_object* v_a_1481_ = stack[6].m_obj;
lean_object* v___y_1482_ = stack[7].m_obj;
lean_object* v___y_1483_ = stack[8].m_obj;
lean_object* v___y_1484_ = stack[9].m_obj;
lean_object* v___y_1485_ = stack[10].m_obj;
lean_object* v___y_1486_ = stack[11].m_obj;
lean_object* v___y_1487_ = stack[12].m_obj;
lean_object* v___y_1488_ = stack[13].m_obj;
lean_object* v___y_1489_ = stack[14].m_obj;
lean_object* v___y_1490_ = stack[15].m_obj;
lean_object* v___y_1491_ = stack[16].m_obj;
lean_object* v_res_1586_;
v_res_1586_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1475_, v_a_1476_, v_a_1477_, v___x_1478_, v_a_1479_, v_e_1480_, v_a_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
stack->m_obj
 = v_res_1586_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_1587_ = _args[0];
lean_object* v_a_1588_ = _args[1];
lean_object* v_a_1589_ = _args[2];
lean_object* v___x_1590_ = _args[3];
lean_object* v_a_1591_ = _args[4];
lean_object* v_e_1592_ = _args[5];
lean_object* v_a_1593_ = _args[6];
lean_object* v___y_1594_ = _args[7];
lean_object* v___y_1595_ = _args[8];
lean_object* v___y_1596_ = _args[9];
lean_object* v___y_1597_ = _args[10];
lean_object* v___y_1598_ = _args[11];
lean_object* v___y_1599_ = _args[12];
lean_object* v___y_1600_ = _args[13];
lean_object* v___y_1601_ = _args[14];
lean_object* v___y_1602_ = _args[15];
lean_object* v___y_1603_ = _args[16];
lean_object* v___y_1604_ = _args[17];
_start:
{
uint8_t v_a_112485__boxed_1605_; uint8_t v___x_112486__boxed_1606_; lean_object* v_res_1607_; 
v_a_112485__boxed_1605_ = lean_unbox(v_a_1589_);
v___x_112486__boxed_1606_ = lean_unbox(v___x_1590_);
v_res_1607_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1587_, v_a_1588_, v_a_112485__boxed_1605_, v___x_112486__boxed_1606_, v_a_1591_, v_e_1592_, v_a_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1607_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(lean_object* v_a_1608_, lean_object* v_a_1609_, uint8_t v_a_1610_, uint8_t v___x_1611_, lean_object* v_e_1612_, lean_object* v_a_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_snd_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1682_; 
v_snd_1625_ = lean_ctor_get(v_a_1613_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_a_1613_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_a_1613_, 0);
lean_dec(v_unused_1683_);
v___x_1627_ = v_a_1613_;
v_isShared_1628_ = v_isSharedCheck_1682_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snd_1625_);
lean_dec(v_a_1613_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1682_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_st_ref_get(v___y_1614_);
lean_inc(v_snd_1625_);
v___x_1631_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1630_, v_snd_1625_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1673_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1673_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1673_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_next_1636_; uint8_t v_ctor_1637_; 
v_next_1636_ = lean_ctor_get(v_a_1632_, 1);
lean_inc_ref(v_next_1636_);
v_ctor_1637_ = lean_ctor_get_uint8(v_a_1632_, sizeof(void*)*12 + 2);
if (v_ctor_1637_ == 0)
{
lean_dec(v_a_1632_);
goto v___jp_1638_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc_ref_n(v_a_1609_, 2);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1629_);
lean_ctor_set(v___x_1652_, 1, v_a_1609_);
lean_inc_ref(v_e_1612_);
lean_inc_ref(v_a_1608_);
v___x_1653_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_1609_, v_a_1632_, v_a_1610_, v___x_1611_, v_a_1608_, v_e_1612_, v___x_1652_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1672_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1672_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1672_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_fst_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1670_; 
v_fst_1658_ = lean_ctor_get(v_a_1654_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1654_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_a_1654_, 1);
lean_dec(v_unused_1671_);
v___x_1660_ = v_a_1654_;
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_fst_1658_);
lean_dec(v_a_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
if (lean_obj_tag(v_fst_1658_) == 0)
{
lean_del_object(v___x_1660_);
lean_del_object(v___x_1656_);
goto v___jp_1638_;
}
else
{
lean_object* v_val_1662_; uint8_t v___x_1663_; 
v_val_1662_ = lean_ctor_get(v_fst_1658_, 0);
v___x_1663_ = lean_unbox(v_val_1662_);
if (v___x_1663_ == 0)
{
lean_dec_ref_known(v_fst_1658_, 1);
lean_del_object(v___x_1660_);
lean_del_object(v___x_1656_);
goto v___jp_1638_;
}
else
{
lean_object* v___x_1665_; 
lean_dec_ref(v_next_1636_);
lean_del_object(v___x_1634_);
lean_del_object(v___x_1627_);
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_a_1608_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_snd_1625_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_fst_1658_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_snd_1625_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1665_);
v___x_1667_ = v___x_1656_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
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
}
else
{
lean_dec_ref(v_next_1636_);
lean_del_object(v___x_1634_);
lean_del_object(v___x_1627_);
lean_dec(v_snd_1625_);
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_a_1608_);
return v___x_1653_;
}
}
v___jp_1638_:
{
size_t v___x_1639_; size_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_ptr_addr(v_next_1636_);
v___x_1640_ = lean_ptr_addr(v_a_1608_);
v___x_1641_ = lean_usize_dec_eq(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1643_; 
lean_del_object(v___x_1634_);
lean_dec(v_snd_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v_next_1636_);
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1643_ = v___x_1627_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_next_1636_);
v___x_1643_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
v_a_1613_ = v___x_1643_;
goto _start;
}
}
else
{
lean_object* v___x_1647_; 
lean_dec_ref(v_next_1636_);
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_a_1608_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1647_ = v___x_1627_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_snd_1625_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1647_);
v___x_1649_ = v___x_1634_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_del_object(v___x_1627_);
lean_dec(v_snd_1625_);
lean_dec_ref(v_e_1612_);
lean_dec_ref(v_a_1609_);
lean_dec_ref(v_a_1608_);
v_a_1674_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1631_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1631_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1608_ = stack[0].m_obj;
lean_object* v_a_1609_ = stack[1].m_obj;
uint8_t v_a_1610_ = stack[2].m_num;
uint8_t v___x_1611_ = stack[3].m_num;
lean_object* v_e_1612_ = stack[4].m_obj;
lean_object* v_a_1613_ = stack[5].m_obj;
lean_object* v___y_1614_ = stack[6].m_obj;
lean_object* v___y_1615_ = stack[7].m_obj;
lean_object* v___y_1616_ = stack[8].m_obj;
lean_object* v___y_1617_ = stack[9].m_obj;
lean_object* v___y_1618_ = stack[10].m_obj;
lean_object* v___y_1619_ = stack[11].m_obj;
lean_object* v___y_1620_ = stack[12].m_obj;
lean_object* v___y_1621_ = stack[13].m_obj;
lean_object* v___y_1622_ = stack[14].m_obj;
lean_object* v___y_1623_ = stack[15].m_obj;
lean_object* v_res_1684_;
v_res_1684_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_1608_, v_a_1609_, v_a_1610_, v___x_1611_, v_e_1612_, v_a_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
stack->m_obj
 = v_res_1684_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_a_1685_ = _args[0];
lean_object* v_a_1686_ = _args[1];
lean_object* v_a_1687_ = _args[2];
lean_object* v___x_1688_ = _args[3];
lean_object* v_e_1689_ = _args[4];
lean_object* v_a_1690_ = _args[5];
lean_object* v___y_1691_ = _args[6];
lean_object* v___y_1692_ = _args[7];
lean_object* v___y_1693_ = _args[8];
lean_object* v___y_1694_ = _args[9];
lean_object* v___y_1695_ = _args[10];
lean_object* v___y_1696_ = _args[11];
lean_object* v___y_1697_ = _args[12];
lean_object* v___y_1698_ = _args[13];
lean_object* v___y_1699_ = _args[14];
lean_object* v___y_1700_ = _args[15];
lean_object* v___y_1701_ = _args[16];
_start:
{
uint8_t v_a_112836__boxed_1702_; uint8_t v___x_112837__boxed_1703_; lean_object* v_res_1704_; 
v_a_112836__boxed_1702_ = lean_unbox(v_a_1687_);
v___x_112837__boxed_1703_ = lean_unbox(v___x_1688_);
v_res_1704_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_1685_, v_a_1686_, v_a_112836__boxed_1702_, v___x_112837__boxed_1703_, v_e_1689_, v_a_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
return v_res_1704_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__6(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__5));
v___x_1719_ = l_Lean_mkConst(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__9(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__8));
v___x_1727_ = l_Lean_mkConst(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateEqUp___closed__12(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__11));
v___x_1735_ = l_Lean_mkConst(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
lean_inc_ref(v_e_1736_);
v___x_1778_ = l_Lean_Expr_cleanupAnnotations(v_e_1736_);
v___x_1779_ = l_Lean_Expr_isApp(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1736_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_arg_1780_ = lean_ctor_get(v___x_1778_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1778_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_arg_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc_ref(v_arg_1783_);
v___x_1784_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1781_);
v___x_1785_ = l_Lean_Expr_isApp(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_arg_1786_ = lean_ctor_get(v___x_1784_, 1);
lean_inc_ref(v_arg_1786_);
v___x_1787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1784_);
v___x_1788_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_1789_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1788_);
lean_dec_ref(v___x_1787_);
if (v___x_1789_ == 0)
{
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1790_; 
lean_inc_ref(v_arg_1783_);
v___x_1790_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1783_, v_a_1737_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1792_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_1780_, v_a_1737_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v_self_1794_; uint8_t v_ctor_1795_; lean_object* v_self_1796_; uint8_t v_ctor_1797_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___x_1981_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v_self_1794_ = lean_ctor_get(v_a_1791_, 0);
lean_inc_ref(v_self_1794_);
v_ctor_1795_ = lean_ctor_get_uint8(v_a_1791_, sizeof(void*)*12 + 2);
lean_dec(v_a_1791_);
v_self_1796_ = lean_ctor_get(v_a_1793_, 0);
lean_inc_ref(v_self_1796_);
v_ctor_1797_ = lean_ctor_get_uint8(v_a_1793_, sizeof(void*)*12 + 2);
lean_dec(v_a_1793_);
v___x_1981_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1741_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; size_t v___x_1983_; size_t v___x_1984_; uint8_t v___x_1985_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = lean_ptr_addr(v_self_1794_);
v___x_1984_ = lean_ptr_addr(v_a_1982_);
v___x_1985_ = lean_usize_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
size_t v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = lean_ptr_addr(v_self_1796_);
v___x_1987_ = lean_usize_dec_eq(v___x_1986_, v___x_1984_);
if (v___x_1987_ == 0)
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_eq(v___x_1983_, v___x_1986_);
if (v___x_1988_ == 0)
{
lean_dec(v_a_1982_);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_st_ref_get(v_a_1737_);
lean_inc_ref(v_e_1736_);
v___x_1990_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1989_, v_e_1736_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v___x_1989_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; size_t v___x_1992_; uint8_t v___x_1993_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_ptr_addr(v_a_1991_);
lean_dec(v_a_1991_);
v___x_1993_ = lean_usize_dec_eq(v___x_1992_, v___x_1984_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_inc(v_a_1746_);
lean_inc_ref(v_a_1745_);
lean_inc(v_a_1744_);
lean_inc_ref(v_a_1743_);
lean_inc(v_a_1742_);
lean_inc_ref(v_a_1741_);
lean_inc(v_a_1740_);
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_arg_1780_);
lean_inc_ref(v_arg_1783_);
v___x_1994_ = lean_grind_mk_eq_proof(v_arg_1783_, v_arg_1780_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
lean_inc_ref_n(v_e_1736_, 2);
v___x_1996_ = l_Lean_Meta_mkEqTrueCore(v_e_1736_, v_a_1995_);
v___x_1997_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1736_, v_a_1982_, v___x_1996_, v___x_1993_, v_a_1737_, v_a_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_dec_ref_known(v___x_1997_, 1);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
else
{
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
return v___x_1997_;
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_a_1982_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1998_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1994_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1994_);
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
else
{
lean_dec(v_a_1982_);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_a_1982_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2006_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1990_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1990_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_st_ref_get(v_a_1737_);
lean_inc_ref(v_e_1736_);
v___x_2015_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2014_, v_e_1736_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; size_t v___x_2017_; uint8_t v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = lean_ptr_addr(v_a_2016_);
lean_dec(v_a_2016_);
v___x_2018_ = lean_usize_dec_eq(v___x_2017_, v___x_1983_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_inc(v_a_1746_);
lean_inc_ref(v_a_1745_);
lean_inc(v_a_1744_);
lean_inc_ref(v_a_1743_);
lean_inc(v_a_1742_);
lean_inc_ref(v_a_1741_);
lean_inc(v_a_1740_);
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_arg_1780_);
v___x_2019_ = lean_grind_mk_eq_proof(v_arg_1780_, v_a_1982_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__9, &l_Lean_Meta_Grind_propagateEqUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__9);
lean_inc_ref(v_arg_1780_);
lean_inc_ref_n(v_arg_1783_, 2);
v___x_2022_ = l_Lean_mkApp3(v___x_2021_, v_arg_1783_, v_arg_1780_, v_a_2020_);
lean_inc_ref(v_e_1736_);
v___x_2023_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1736_, v_arg_1783_, v___x_2022_, v___x_2018_, v_a_1737_, v_a_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_dec_ref_known(v___x_2023_, 1);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
else
{
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
return v___x_2023_;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2024_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2019_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2019_);
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
else
{
lean_dec(v_a_1982_);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_1982_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2032_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2015_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2015_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_st_ref_get(v_a_1737_);
lean_inc_ref(v_e_1736_);
v___x_2041_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_2040_, v_e_1736_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; size_t v___x_2043_; size_t v___x_2044_; uint8_t v___x_2045_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = lean_ptr_addr(v_a_2042_);
lean_dec(v_a_2042_);
v___x_2044_ = lean_ptr_addr(v_self_1796_);
v___x_2045_ = lean_usize_dec_eq(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_inc(v_a_1746_);
lean_inc_ref(v_a_1745_);
lean_inc(v_a_1744_);
lean_inc_ref(v_a_1743_);
lean_inc(v_a_1742_);
lean_inc_ref(v_a_1741_);
lean_inc(v_a_1740_);
lean_inc_ref(v_a_1739_);
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_inc_ref(v_arg_1783_);
v___x_2046_ = lean_grind_mk_eq_proof(v_arg_1783_, v_a_1982_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__12, &l_Lean_Meta_Grind_propagateEqUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__12);
lean_inc_ref_n(v_arg_1780_, 2);
lean_inc_ref(v_arg_1783_);
v___x_2049_ = l_Lean_mkApp3(v___x_2048_, v_arg_1783_, v_arg_1780_, v_a_2047_);
lean_inc_ref(v_e_1736_);
v___x_2050_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1736_, v_arg_1780_, v___x_2049_, v___x_2045_, v_a_1737_, v_a_1739_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_dec_ref_known(v___x_2050_, 1);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
else
{
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
return v___x_2050_;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2051_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2046_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2046_);
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
else
{
lean_dec(v_a_1982_);
v___y_1847_ = v_a_1737_;
v___y_1848_ = v_a_1738_;
v___y_1849_ = v_a_1739_;
v___y_1850_ = v_a_1740_;
v___y_1851_ = v_a_1741_;
v___y_1852_ = v_a_1742_;
v___y_1853_ = v_a_1743_;
v___y_1854_ = v_a_1744_;
v___y_1855_ = v_a_1745_;
v___y_1856_ = v_a_1746_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_1982_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2059_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2041_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2041_);
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
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2067_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1981_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1981_);
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
v___jp_1798_:
{
size_t v___x_1812_; size_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = lean_ptr_addr(v_self_1794_);
lean_dec_ref(v_self_1794_);
v___x_1813_ = lean_ptr_addr(v___y_1807_);
lean_dec_ref(v___y_1807_);
v___x_1814_ = lean_usize_dec_eq(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1772_;
}
else
{
size_t v___x_1815_; size_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_ptr_addr(v_self_1796_);
lean_dec_ref(v_self_1796_);
v___x_1816_ = lean_ptr_addr(v___y_1801_);
lean_dec_ref(v___y_1801_);
v___x_1817_ = lean_usize_dec_eq(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1772_;
}
else
{
lean_object* v___x_1818_; 
lean_inc_ref(v_arg_1783_);
v___x_1818_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1783_, v___y_1803_, v___y_1804_, v___y_1799_, v___y_1811_, v___y_1808_, v___y_1800_, v___y_1802_, v___y_1809_, v___y_1810_, v___y_1805_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1820_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1780_, v___y_1803_, v___y_1804_, v___y_1799_, v___y_1811_, v___y_1808_, v___y_1800_, v___y_1802_, v___y_1809_, v___y_1810_, v___y_1805_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__2));
v___x_1823_ = ((lean_object*)(l_Lean_Meta_Grind_propagateAndUp___closed__3));
v___x_1824_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__2));
lean_inc_ref(v___y_1806_);
v___x_1825_ = l_Lean_Name_mkStr4(v___x_1822_, v___x_1823_, v___y_1806_, v___x_1824_);
v___x_1826_ = lean_box(0);
v___x_1827_ = l_Lean_mkConst(v___x_1825_, v___x_1826_);
v___x_1828_ = l_Lean_mkApp4(v___x_1827_, v_arg_1783_, v_arg_1780_, v_a_1819_, v_a_1821_);
v___x_1829_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1736_, v___x_1828_, v___y_1803_, v___y_1799_, v___y_1808_, v___y_1802_, v___y_1809_, v___y_1810_, v___y_1805_);
return v___x_1829_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1819_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1830_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1820_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1820_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1838_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1818_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1818_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
v___jp_1846_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1857_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolDiseq___closed__0));
v___x_1858_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
v___x_1859_ = l_Lean_Expr_isConstOf(v_arg_1786_, v___x_1858_);
lean_dec_ref(v_arg_1786_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_inc_ref(v_e_1736_);
v___x_1860_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1736_, v___y_1847_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1911_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1911_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1911_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_unbox(v_a_1861_);
if (v___x_1865_ == 0)
{
lean_del_object(v___x_1863_);
if (v_ctor_1795_ == 0)
{
lean_dec(v_a_1861_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1769_;
}
else
{
if (v_ctor_1797_ == 0)
{
lean_dec(v_a_1861_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1769_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = l_Lean_Expr_getAppFn(v_self_1794_);
v___x_1867_ = l_Lean_Expr_getAppFn(v_self_1796_);
v___x_1868_ = lean_expr_eqv(v___x_1866_, v___x_1867_);
lean_dec_ref(v___x_1867_);
lean_dec_ref(v___x_1866_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___f_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_box(v___x_1789_);
lean_inc_ref(v_self_1796_);
lean_inc_ref(v_arg_1780_);
lean_inc_ref(v_arg_1783_);
lean_inc_ref(v_self_1794_);
lean_inc(v_a_1861_);
v___f_1870_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 18, 6);
lean_closure_set(v___f_1870_, 0, v_a_1861_);
lean_closure_set(v___f_1870_, 1, v___x_1869_);
lean_closure_set(v___f_1870_, 2, v_self_1794_);
lean_closure_set(v___f_1870_, 3, v_arg_1783_);
lean_closure_set(v___f_1870_, 4, v_arg_1780_);
lean_closure_set(v___f_1870_, 5, v_self_1796_);
v___x_1871_ = l_Lean_Meta_Grind_hasSameType(v_self_1794_, v_self_1796_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; uint8_t v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = lean_unbox(v_a_1872_);
lean_dec(v_a_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v___f_1870_);
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_box(0);
lean_inc_ref(v_arg_1783_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_arg_1783_);
v___x_1877_ = lean_unbox(v_a_1861_);
lean_dec(v_a_1861_);
v___x_1878_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_arg_1783_, v_arg_1780_, v___x_1877_, v___x_1789_, v_e_1736_, v___x_1876_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v___x_1878_, 0);
lean_dec(v_unused_1886_);
v___x_1880_ = v___x_1878_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v___x_1878_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1874_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1874_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
v_a_1887_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1878_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1878_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v___x_1895_; 
lean_dec(v_a_1861_);
v___x_1895_ = l_Lean_Meta_mkEq(v_arg_1783_, v_arg_1780_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__4));
v___x_1898_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v___x_1897_, v_a_1896_, v___f_1870_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
v___y_1749_ = v___y_1856_;
v___y_1750_ = v___y_1849_;
v___y_1751_ = v___y_1853_;
v___y_1752_ = v___y_1851_;
v___y_1753_ = v___y_1847_;
v___y_1754_ = v___y_1854_;
v___y_1755_ = v___y_1855_;
v___y_1756_ = v___x_1898_;
goto v___jp_1748_;
}
else
{
lean_dec_ref(v___f_1870_);
v___y_1749_ = v___y_1856_;
v___y_1750_ = v___y_1849_;
v___y_1751_ = v___y_1853_;
v___y_1752_ = v___y_1851_;
v___y_1753_ = v___y_1847_;
v___y_1754_ = v___y_1854_;
v___y_1755_ = v___y_1855_;
v___y_1756_ = v___x_1895_;
goto v___jp_1748_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v___f_1870_);
lean_dec(v_a_1861_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1899_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1871_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1871_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_dec(v_a_1861_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
goto v___jp_1769_;
}
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec(v_a_1861_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v___x_1907_ = lean_box(0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1907_);
v___x_1909_ = v___x_1863_;
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
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1912_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1860_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1860_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v___x_1920_; 
lean_inc_ref(v_e_1736_);
v___x_1920_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1736_, v___y_1847_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; uint8_t v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = lean_unbox(v_a_1921_);
lean_dec(v_a_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_1851_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_1851_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; size_t v___x_1927_; size_t v___x_1928_; uint8_t v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = lean_ptr_addr(v_self_1794_);
v___x_1928_ = lean_ptr_addr(v_a_1924_);
v___x_1929_ = lean_usize_dec_eq(v___x_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
v___y_1799_ = v___y_1849_;
v___y_1800_ = v___y_1852_;
v___y_1801_ = v_a_1924_;
v___y_1802_ = v___y_1853_;
v___y_1803_ = v___y_1847_;
v___y_1804_ = v___y_1848_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___x_1857_;
v___y_1807_ = v_a_1926_;
v___y_1808_ = v___y_1851_;
v___y_1809_ = v___y_1854_;
v___y_1810_ = v___y_1855_;
v___y_1811_ = v___y_1850_;
goto v___jp_1798_;
}
else
{
size_t v___x_1930_; size_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_ptr_addr(v_self_1796_);
v___x_1931_ = lean_ptr_addr(v_a_1926_);
v___x_1932_ = lean_usize_dec_eq(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
v___y_1799_ = v___y_1849_;
v___y_1800_ = v___y_1852_;
v___y_1801_ = v_a_1924_;
v___y_1802_ = v___y_1853_;
v___y_1803_ = v___y_1847_;
v___y_1804_ = v___y_1848_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___x_1857_;
v___y_1807_ = v_a_1926_;
v___y_1808_ = v___y_1851_;
v___y_1809_ = v___y_1854_;
v___y_1810_ = v___y_1855_;
v___y_1811_ = v___y_1850_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1933_; 
lean_dec(v_a_1926_);
lean_dec(v_a_1924_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_inc_ref(v_arg_1783_);
v___x_1933_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_1783_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1935_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_1780_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = lean_obj_once(&l_Lean_Meta_Grind_propagateEqUp___closed__6, &l_Lean_Meta_Grind_propagateEqUp___closed__6_once, _init_l_Lean_Meta_Grind_propagateEqUp___closed__6);
v___x_1938_ = l_Lean_mkApp4(v___x_1937_, v_arg_1783_, v_arg_1780_, v_a_1934_, v_a_1936_);
v___x_1939_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1736_, v___x_1938_, v___y_1847_, v___y_1849_, v___y_1851_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1934_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1940_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1935_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1935_);
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
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1948_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1933_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1933_);
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
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1924_);
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1956_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1925_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1925_);
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
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1964_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1923_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1923_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v___x_1972_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
v___x_1972_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_1736_, v_arg_1783_, v_arg_1780_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1972_;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_self_1796_);
lean_dec_ref(v_self_1794_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_1973_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1920_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1920_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_1791_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2075_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_1792_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_1792_);
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
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1736_);
v_a_2083_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_1790_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_1790_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
}
v___jp_1748_:
{
if (lean_obj_tag(v___y_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1757_ = lean_ctor_get(v___y_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___y_1756_, 1);
v___x_1758_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg___closed__2);
lean_inc_ref(v_e_1736_);
v___x_1759_ = l_Lean_mkAppB(v___x_1758_, v_e_1736_, v_a_1757_);
v___x_1760_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1736_, v___x_1759_, v___y_1753_, v___y_1750_, v___y_1752_, v___y_1751_, v___y_1754_, v___y_1755_, v___y_1749_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v_e_1736_);
v_a_1761_ = lean_ctor_get(v___y_1756_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___y_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___y_1756_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___y_1756_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
v___jp_1769_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
v___jp_1772_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateEqUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1736_ = stack[0].m_obj;
lean_object* v_a_1737_ = stack[1].m_obj;
lean_object* v_a_1738_ = stack[2].m_obj;
lean_object* v_a_1739_ = stack[3].m_obj;
lean_object* v_a_1740_ = stack[4].m_obj;
lean_object* v_a_1741_ = stack[5].m_obj;
lean_object* v_a_1742_ = stack[6].m_obj;
lean_object* v_a_1743_ = stack[7].m_obj;
lean_object* v_a_1744_ = stack[8].m_obj;
lean_object* v_a_1745_ = stack[9].m_obj;
lean_object* v_a_1746_ = stack[10].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l_Lean_Meta_Grind_propagateEqUp(v_e_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___boxed(lean_object* v_e_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Meta_Grind_propagateEqUp(v_e_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec(v_a_2093_);
return v_res_2104_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_object* v_00_u03b1_2105_, lean_object* v_name_2106_, uint8_t v_bi_2107_, lean_object* v_type_2108_, lean_object* v_k_2109_, uint8_t v_kind_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___redArg(v_name_2106_, v_bi_2107_, v_type_2108_, v_k_2109_, v_kind_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2106_ = stack[1].m_obj;
uint8_t v_bi_2107_ = stack[2].m_num;
lean_object* v_type_2108_ = stack[3].m_obj;
lean_object* v_k_2109_ = stack[4].m_obj;
uint8_t v_kind_2110_ = stack[5].m_num;
lean_object* v___y_2111_ = stack[6].m_obj;
lean_object* v___y_2112_ = stack[7].m_obj;
lean_object* v___y_2113_ = stack[8].m_obj;
lean_object* v___y_2114_ = stack[9].m_obj;
lean_object* v___y_2115_ = stack[10].m_obj;
lean_object* v___y_2116_ = stack[11].m_obj;
lean_object* v___y_2117_ = stack[12].m_obj;
lean_object* v___y_2118_ = stack[13].m_obj;
lean_object* v___y_2119_ = stack[14].m_obj;
lean_object* v___y_2120_ = stack[15].m_obj;
lean_object* v_res_2123_;
v_res_2123_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(lean_box(0), v_name_2106_, v_bi_2107_, v_type_2108_, v_k_2109_, v_kind_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
stack->m_obj
 = v_res_2123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_2124_ = _args[0];
lean_object* v_name_2125_ = _args[1];
lean_object* v_bi_2126_ = _args[2];
lean_object* v_type_2127_ = _args[3];
lean_object* v_k_2128_ = _args[4];
lean_object* v_kind_2129_ = _args[5];
lean_object* v___y_2130_ = _args[6];
lean_object* v___y_2131_ = _args[7];
lean_object* v___y_2132_ = _args[8];
lean_object* v___y_2133_ = _args[9];
lean_object* v___y_2134_ = _args[10];
lean_object* v___y_2135_ = _args[11];
lean_object* v___y_2136_ = _args[12];
lean_object* v___y_2137_ = _args[13];
lean_object* v___y_2138_ = _args[14];
lean_object* v___y_2139_ = _args[15];
lean_object* v___y_2140_ = _args[16];
_start:
{
uint8_t v_bi_boxed_2141_; uint8_t v_kind_boxed_2142_; lean_object* v_res_2143_; 
v_bi_boxed_2141_ = lean_unbox(v_bi_2126_);
v_kind_boxed_2142_ = lean_unbox(v_kind_2129_);
v_res_2143_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_spec__0(v_00_u03b1_2124_, v_name_2125_, v_bi_boxed_2141_, v_type_2127_, v_k_2128_, v_kind_boxed_2142_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
return v_res_2143_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_object* v_00_u03b1_2144_, lean_object* v_name_2145_, lean_object* v_type_2146_, lean_object* v_k_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0___redArg(v_name_2145_, v_type_2146_, v_k_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2145_ = stack[1].m_obj;
lean_object* v_type_2146_ = stack[2].m_obj;
lean_object* v_k_2147_ = stack[3].m_obj;
lean_object* v___y_2148_ = stack[4].m_obj;
lean_object* v___y_2149_ = stack[5].m_obj;
lean_object* v___y_2150_ = stack[6].m_obj;
lean_object* v___y_2151_ = stack[7].m_obj;
lean_object* v___y_2152_ = stack[8].m_obj;
lean_object* v___y_2153_ = stack[9].m_obj;
lean_object* v___y_2154_ = stack[10].m_obj;
lean_object* v___y_2155_ = stack[11].m_obj;
lean_object* v___y_2156_ = stack[12].m_obj;
lean_object* v___y_2157_ = stack[13].m_obj;
lean_object* v_res_2160_;
v_res_2160_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_propagateEqUp_spec__0(lean_box(0), v_name_2145_, v_type_2146_, v_k_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
stack->m_obj
 = v_res_2160_;
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
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(lean_object* v_a_2177_, lean_object* v_a_2178_, uint8_t v_a_2179_, uint8_t v___x_2180_, lean_object* v_a_2181_, lean_object* v_e_2182_, lean_object* v_inst_2183_, lean_object* v_a_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___redArg(v_a_2177_, v_a_2178_, v_a_2179_, v___x_2180_, v_a_2181_, v_e_2182_, v_a_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2177_ = stack[0].m_obj;
lean_object* v_a_2178_ = stack[1].m_obj;
uint8_t v_a_2179_ = stack[2].m_num;
uint8_t v___x_2180_ = stack[3].m_num;
lean_object* v_a_2181_ = stack[4].m_obj;
lean_object* v_e_2182_ = stack[5].m_obj;
lean_object* v_a_2184_ = stack[7].m_obj;
lean_object* v___y_2185_ = stack[8].m_obj;
lean_object* v___y_2186_ = stack[9].m_obj;
lean_object* v___y_2187_ = stack[10].m_obj;
lean_object* v___y_2188_ = stack[11].m_obj;
lean_object* v___y_2189_ = stack[12].m_obj;
lean_object* v___y_2190_ = stack[13].m_obj;
lean_object* v___y_2191_ = stack[14].m_obj;
lean_object* v___y_2192_ = stack[15].m_obj;
lean_object* v___y_2193_ = stack[16].m_obj;
lean_object* v___y_2194_ = stack[17].m_obj;
lean_object* v_res_2197_;
v_res_2197_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(v_a_2177_, v_a_2178_, v_a_2179_, v___x_2180_, v_a_2181_, v_e_2182_, lean_box(0), v_a_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1___boxed(lean_object** _args){
lean_object* v_a_2198_ = _args[0];
lean_object* v_a_2199_ = _args[1];
lean_object* v_a_2200_ = _args[2];
lean_object* v___x_2201_ = _args[3];
lean_object* v_a_2202_ = _args[4];
lean_object* v_e_2203_ = _args[5];
lean_object* v_inst_2204_ = _args[6];
lean_object* v_a_2205_ = _args[7];
lean_object* v___y_2206_ = _args[8];
lean_object* v___y_2207_ = _args[9];
lean_object* v___y_2208_ = _args[10];
lean_object* v___y_2209_ = _args[11];
lean_object* v___y_2210_ = _args[12];
lean_object* v___y_2211_ = _args[13];
lean_object* v___y_2212_ = _args[14];
lean_object* v___y_2213_ = _args[15];
lean_object* v___y_2214_ = _args[16];
lean_object* v___y_2215_ = _args[17];
lean_object* v___y_2216_ = _args[18];
_start:
{
uint8_t v_a_114368__boxed_2217_; uint8_t v___x_114369__boxed_2218_; lean_object* v_res_2219_; 
v_a_114368__boxed_2217_ = lean_unbox(v_a_2200_);
v___x_114369__boxed_2218_ = lean_unbox(v___x_2201_);
v_res_2219_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1(v_a_2198_, v_a_2199_, v_a_114368__boxed_2217_, v___x_114369__boxed_2218_, v_a_2202_, v_e_2203_, v_inst_2204_, v_a_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec(v___y_2206_);
return v_res_2219_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(lean_object* v_a_2220_, lean_object* v_a_2221_, uint8_t v_a_2222_, uint8_t v___x_2223_, lean_object* v_e_2224_, lean_object* v_inst_2225_, lean_object* v_a_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___redArg(v_a_2220_, v_a_2221_, v_a_2222_, v___x_2223_, v_e_2224_, v_a_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2220_ = stack[0].m_obj;
lean_object* v_a_2221_ = stack[1].m_obj;
uint8_t v_a_2222_ = stack[2].m_num;
uint8_t v___x_2223_ = stack[3].m_num;
lean_object* v_e_2224_ = stack[4].m_obj;
lean_object* v_a_2226_ = stack[6].m_obj;
lean_object* v___y_2227_ = stack[7].m_obj;
lean_object* v___y_2228_ = stack[8].m_obj;
lean_object* v___y_2229_ = stack[9].m_obj;
lean_object* v___y_2230_ = stack[10].m_obj;
lean_object* v___y_2231_ = stack[11].m_obj;
lean_object* v___y_2232_ = stack[12].m_obj;
lean_object* v___y_2233_ = stack[13].m_obj;
lean_object* v___y_2234_ = stack[14].m_obj;
lean_object* v___y_2235_ = stack[15].m_obj;
lean_object* v___y_2236_ = stack[16].m_obj;
lean_object* v_res_2239_;
v_res_2239_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(v_a_2220_, v_a_2221_, v_a_2222_, v___x_2223_, v_e_2224_, lean_box(0), v_a_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
stack->m_obj
 = v_res_2239_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2___boxed(lean_object** _args){
lean_object* v_a_2240_ = _args[0];
lean_object* v_a_2241_ = _args[1];
lean_object* v_a_2242_ = _args[2];
lean_object* v___x_2243_ = _args[3];
lean_object* v_e_2244_ = _args[4];
lean_object* v_inst_2245_ = _args[5];
lean_object* v_a_2246_ = _args[6];
lean_object* v___y_2247_ = _args[7];
lean_object* v___y_2248_ = _args[8];
lean_object* v___y_2249_ = _args[9];
lean_object* v___y_2250_ = _args[10];
lean_object* v___y_2251_ = _args[11];
lean_object* v___y_2252_ = _args[12];
lean_object* v___y_2253_ = _args[13];
lean_object* v___y_2254_ = _args[14];
lean_object* v___y_2255_ = _args[15];
lean_object* v___y_2256_ = _args[16];
lean_object* v___y_2257_ = _args[17];
_start:
{
uint8_t v_a_114456__boxed_2258_; uint8_t v___x_114457__boxed_2259_; lean_object* v_res_2260_; 
v_a_114456__boxed_2258_ = lean_unbox(v_a_2242_);
v___x_114457__boxed_2259_ = lean_unbox(v___x_2243_);
v_res_2260_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__2(v_a_2240_, v_a_2241_, v_a_114456__boxed_2258_, v___x_114457__boxed_2259_, v_e_2244_, v_inst_2245_, v_a_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
return v_res_2260_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_e_2263_, uint8_t v___x_2264_, uint8_t v_a_2265_, lean_object* v_a_2266_, lean_object* v_inst_2267_, lean_object* v_a_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___redArg(v_a_2261_, v_a_2262_, v_e_2263_, v___x_2264_, v_a_2265_, v_a_2266_, v_a_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2261_ = stack[0].m_obj;
lean_object* v_a_2262_ = stack[1].m_obj;
lean_object* v_e_2263_ = stack[2].m_obj;
uint8_t v___x_2264_ = stack[3].m_num;
uint8_t v_a_2265_ = stack[4].m_num;
lean_object* v_a_2266_ = stack[5].m_obj;
lean_object* v_a_2268_ = stack[7].m_obj;
lean_object* v___y_2269_ = stack[8].m_obj;
lean_object* v___y_2270_ = stack[9].m_obj;
lean_object* v___y_2271_ = stack[10].m_obj;
lean_object* v___y_2272_ = stack[11].m_obj;
lean_object* v___y_2273_ = stack[12].m_obj;
lean_object* v___y_2274_ = stack[13].m_obj;
lean_object* v___y_2275_ = stack[14].m_obj;
lean_object* v___y_2276_ = stack[15].m_obj;
lean_object* v___y_2277_ = stack[16].m_obj;
lean_object* v___y_2278_ = stack[17].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(v_a_2261_, v_a_2262_, v_e_2263_, v___x_2264_, v_a_2265_, v_a_2266_, lean_box(0), v_a_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2___boxed(lean_object** _args){
lean_object* v_a_2282_ = _args[0];
lean_object* v_a_2283_ = _args[1];
lean_object* v_e_2284_ = _args[2];
lean_object* v___x_2285_ = _args[3];
lean_object* v_a_2286_ = _args[4];
lean_object* v_a_2287_ = _args[5];
lean_object* v_inst_2288_ = _args[6];
lean_object* v_a_2289_ = _args[7];
lean_object* v___y_2290_ = _args[8];
lean_object* v___y_2291_ = _args[9];
lean_object* v___y_2292_ = _args[10];
lean_object* v___y_2293_ = _args[11];
lean_object* v___y_2294_ = _args[12];
lean_object* v___y_2295_ = _args[13];
lean_object* v___y_2296_ = _args[14];
lean_object* v___y_2297_ = _args[15];
lean_object* v___y_2298_ = _args[16];
lean_object* v___y_2299_ = _args[17];
lean_object* v___y_2300_ = _args[18];
_start:
{
uint8_t v___x_114539__boxed_2301_; uint8_t v_a_114540__boxed_2302_; lean_object* v_res_2303_; 
v___x_114539__boxed_2301_ = lean_unbox(v___x_2285_);
v_a_114540__boxed_2302_ = lean_unbox(v_a_2286_);
v_res_2303_ = l___private_Init_While_0__repeatM_erased___at___00__private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateEqUp_spec__1_spec__2(v_a_2282_, v_a_2283_, v_e_2284_, v___x_114539__boxed_2301_, v_a_114540__boxed_2302_, v_a_2287_, v_inst_2288_, v_a_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec(v___y_2290_);
return v_res_2303_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2306_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___boxed), 12, 0);
v___x_2307_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2305_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2308_;
v_res_2308_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9____boxed(lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqUp___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_286357030____hygCtx___hyg_9_();
return v_res_2310_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* v_e_2311_, lean_object* v_as_2312_, size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec_ref(v_e_2311_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v_b_2315_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2331_; 
v___x_2329_ = lean_box(0);
v_a_2330_ = lean_array_uget_borrowed(v_as_2312_, v_i_2314_);
lean_inc_ref(v_e_2311_);
lean_inc(v_a_2330_);
v___x_2331_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_a_2330_, v_e_2311_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2331_) == 0)
{
size_t v___x_2332_; size_t v___x_2333_; 
lean_dec_ref_known(v___x_2331_, 1);
v___x_2332_ = ((size_t)1ULL);
v___x_2333_ = lean_usize_add(v_i_2314_, v___x_2332_);
v_i_2314_ = v___x_2333_;
v_b_2315_ = v___x_2329_;
goto _start;
}
else
{
lean_dec_ref(v_e_2311_);
return v___x_2331_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2311_ = stack[0].m_obj;
lean_object* v_as_2312_ = stack[1].m_obj;
size_t v_sz_2313_ = stack[2].m_num;
size_t v_i_2314_ = stack[3].m_num;
lean_object* v_b_2315_ = stack[4].m_obj;
lean_object* v___y_2316_ = stack[5].m_obj;
lean_object* v___y_2317_ = stack[6].m_obj;
lean_object* v___y_2318_ = stack[7].m_obj;
lean_object* v___y_2319_ = stack[8].m_obj;
lean_object* v___y_2320_ = stack[9].m_obj;
lean_object* v___y_2321_ = stack[10].m_obj;
lean_object* v___y_2322_ = stack[11].m_obj;
lean_object* v___y_2323_ = stack[12].m_obj;
lean_object* v___y_2324_ = stack[13].m_obj;
lean_object* v___y_2325_ = stack[14].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2311_, v_as_2312_, v_sz_2313_, v_i_2314_, v_b_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* v_e_2336_, lean_object* v_as_2337_, lean_object* v_sz_2338_, lean_object* v_i_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2338_);
lean_dec(v_sz_2338_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2336_, v_as_2337_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v_as_2337_);
return v_res_2354_;
}
}
lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* v_e_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2379_; 
lean_inc_ref(v_e_2358_);
v___x_2379_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2358_, v_a_2359_, v_a_2363_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; uint8_t v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = lean_unbox(v_a_2380_);
lean_dec(v_a_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
lean_inc_ref(v_e_2358_);
v___x_2382_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2358_, v_a_2359_, v_a_2363_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2497_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2497_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2497_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
uint8_t v___x_2387_; 
v___x_2387_ = lean_unbox(v_a_2383_);
lean_dec(v_a_2383_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec_ref(v_e_2358_);
v___x_2388_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2388_);
v___x_2390_ = v___x_2385_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
else
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
lean_del_object(v___x_2385_);
lean_inc_ref(v_e_2358_);
v___x_2392_ = l_Lean_Expr_cleanupAnnotations(v_e_2358_);
v___x_2393_ = l_Lean_Expr_isApp(v___x_2392_);
if (v___x_2393_ == 0)
{
lean_dec_ref(v___x_2392_);
lean_dec_ref(v_e_2358_);
goto v___jp_2370_;
}
else
{
lean_object* v_arg_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_arg_2394_ = lean_ctor_get(v___x_2392_, 1);
lean_inc_ref(v_arg_2394_);
v___x_2395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2392_);
v___x_2396_ = l_Lean_Expr_isApp(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec_ref(v___x_2395_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
goto v___jp_2370_;
}
else
{
lean_object* v_arg_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_arg_2397_ = lean_ctor_get(v___x_2395_, 1);
lean_inc_ref(v_arg_2397_);
v___x_2398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2395_);
v___x_2399_ = l_Lean_Expr_isApp(v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec_ref(v___x_2398_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
goto v___jp_2370_;
}
else
{
lean_object* v_arg_2400_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v_arg_2400_ = lean_ctor_get(v___x_2398_, 1);
lean_inc_ref(v_arg_2400_);
v___x_2491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2398_);
v___x_2492_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2493_ = l_Lean_Expr_isConstOf(v___x_2491_, v___x_2492_);
lean_dec_ref(v___x_2491_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
goto v___jp_2370_;
}
else
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__3));
v___x_2495_ = l_Lean_Expr_isConstOf(v_arg_2400_, v___x_2494_);
if (v___x_2495_ == 0)
{
v___y_2435_ = v_a_2359_;
v___y_2436_ = v_a_2360_;
v___y_2437_ = v_a_2361_;
v___y_2438_ = v_a_2362_;
v___y_2439_ = v_a_2363_;
v___y_2440_ = v_a_2364_;
v___y_2441_ = v_a_2365_;
v___y_2442_ = v_a_2366_;
v___y_2443_ = v_a_2367_;
v___y_2444_ = v_a_2368_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2496_; 
lean_inc_ref(v_arg_2394_);
lean_inc_ref(v_arg_2397_);
lean_inc_ref(v_e_2358_);
v___x_2496_ = l_Lean_Meta_Grind_propagateBoolDiseq(v_e_2358_, v_arg_2397_, v_arg_2394_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_dec_ref_known(v___x_2496_, 1);
v___y_2435_ = v_a_2359_;
v___y_2436_ = v_a_2360_;
v___y_2437_ = v_a_2361_;
v___y_2438_ = v_a_2362_;
v___y_2439_ = v_a_2363_;
v___y_2440_ = v_a_2364_;
v___y_2441_ = v_a_2365_;
v___y_2442_ = v_a_2366_;
v___y_2443_ = v_a_2367_;
v___y_2444_ = v_a_2368_;
goto v___jp_2434_;
}
else
{
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
return v___x_2496_;
}
}
}
v___jp_2401_:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2400_, v___y_2406_, v___y_2408_, v___y_2410_, v___y_2402_, v___y_2404_, v___y_2411_, v___y_2405_, v___y_2407_, v___y_2403_, v___y_2409_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; size_t v_sz_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = lean_box(0);
v_sz_2415_ = lean_array_size(v_a_2413_);
v___x_2416_ = ((size_t)0ULL);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateEqDown_spec__0(v_e_2358_, v_a_2413_, v_sz_2415_, v___x_2416_, v___x_2414_, v___y_2406_, v___y_2408_, v___y_2410_, v___y_2402_, v___y_2404_, v___y_2411_, v___y_2405_, v___y_2407_, v___y_2403_, v___y_2409_);
lean_dec(v_a_2413_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2417_, 0);
lean_dec(v_unused_2425_);
v___x_2419_ = v___x_2417_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_dec(v___x_2417_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2414_);
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2414_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
return v___x_2417_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v_e_2358_);
v_a_2426_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2412_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2412_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
v___jp_2434_:
{
lean_object* v___x_2445_; 
lean_inc_ref(v_arg_2394_);
lean_inc_ref(v_arg_2397_);
v___x_2445_ = l_Lean_Meta_Grind_Solvers_propagateDiseqs(v_arg_2397_, v_arg_2394_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref_known(v___x_2445_, 1);
lean_inc_ref(v_arg_2400_);
v___x_2446_ = l_Lean_Meta_Grind_getExtTheorems(v_arg_2400_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2482_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2482_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2482_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2451_ = lean_array_get_size(v_a_2447_);
lean_dec(v_a_2447_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_nat_dec_eq(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_del_object(v___x_2449_);
v___x_2454_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2397_, v___y_2435_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2456_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_2394_, v___y_2435_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqDown___closed__1));
v___x_2459_ = l_Lean_Expr_isAppOf(v_arg_2400_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec(v_a_2457_);
lean_dec(v_a_2455_);
v___y_2402_ = v___y_2438_;
v___y_2403_ = v___y_2443_;
v___y_2404_ = v___y_2439_;
v___y_2405_ = v___y_2441_;
v___y_2406_ = v___y_2435_;
v___y_2407_ = v___y_2442_;
v___y_2408_ = v___y_2436_;
v___y_2409_ = v___y_2444_;
v___y_2410_ = v___y_2437_;
v___y_2411_ = v___y_2440_;
goto v___jp_2401_;
}
else
{
uint8_t v_ctor_2460_; 
v_ctor_2460_ = lean_ctor_get_uint8(v_a_2455_, sizeof(void*)*12 + 2);
lean_dec(v_a_2455_);
if (v_ctor_2460_ == 0)
{
uint8_t v_ctor_2461_; 
v_ctor_2461_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*12 + 2);
lean_dec(v_a_2457_);
if (v_ctor_2461_ == 0)
{
v___y_2402_ = v___y_2438_;
v___y_2403_ = v___y_2443_;
v___y_2404_ = v___y_2439_;
v___y_2405_ = v___y_2441_;
v___y_2406_ = v___y_2435_;
v___y_2407_ = v___y_2442_;
v___y_2408_ = v___y_2436_;
v___y_2409_ = v___y_2444_;
v___y_2410_ = v___y_2437_;
v___y_2411_ = v___y_2440_;
goto v___jp_2401_;
}
else
{
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_e_2358_);
goto v___jp_2376_;
}
}
else
{
lean_dec(v_a_2457_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_e_2358_);
goto v___jp_2376_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2455_);
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_e_2358_);
v_a_2462_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2456_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2456_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
v_a_2470_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2454_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2454_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
v___x_2478_ = lean_box(0);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2478_);
v___x_2480_ = v___x_2449_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
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
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
v_a_2483_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2446_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2446_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2400_);
lean_dec_ref(v_arg_2397_);
lean_dec_ref(v_arg_2394_);
lean_dec_ref(v_e_2358_);
return v___x_2445_;
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
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref(v_e_2358_);
v_a_2498_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2382_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2382_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v___x_2506_; uint8_t v___x_2507_; 
lean_inc_ref(v_e_2358_);
v___x_2506_ = l_Lean_Expr_cleanupAnnotations(v_e_2358_);
v___x_2507_ = l_Lean_Expr_isApp(v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v___x_2506_);
lean_dec_ref(v_e_2358_);
goto v___jp_2373_;
}
else
{
lean_object* v_arg_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_arg_2508_ = lean_ctor_get(v___x_2506_, 1);
lean_inc_ref(v_arg_2508_);
v___x_2509_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2506_);
v___x_2510_ = l_Lean_Expr_isApp(v___x_2509_);
if (v___x_2510_ == 0)
{
lean_dec_ref(v___x_2509_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
goto v___jp_2373_;
}
else
{
lean_object* v_arg_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_arg_2511_ = lean_ctor_get(v___x_2509_, 1);
lean_inc_ref(v_arg_2511_);
v___x_2512_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2509_);
v___x_2513_ = l_Lean_Expr_isApp(v___x_2512_);
if (v___x_2513_ == 0)
{
lean_dec_ref(v___x_2512_);
lean_dec_ref(v_arg_2511_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
goto v___jp_2373_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2512_);
v___x_2515_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2516_ = l_Lean_Expr_isConstOf(v___x_2514_, v___x_2515_);
lean_dec_ref(v___x_2514_);
if (v___x_2516_ == 0)
{
lean_dec_ref(v_arg_2511_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
goto v___jp_2373_;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2511_, v_arg_2508_, v_a_2359_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2540_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_unbox(v_a_2518_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; 
lean_del_object(v___x_2520_);
lean_inc_ref(v_e_2358_);
v___x_2523_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2358_, v_a_2524_);
v___x_2526_ = lean_unbox(v_a_2518_);
lean_dec(v_a_2518_);
v___x_2527_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2511_, v_arg_2508_, v___x_2525_, v___x_2526_, v_a_2359_, v_a_2361_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2527_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v_a_2518_);
lean_dec_ref(v_arg_2511_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
v_a_2528_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2523_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_a_2518_);
lean_dec_ref(v_arg_2511_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
v___x_2536_ = lean_box(0);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2536_);
v___x_2538_ = v___x_2520_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_arg_2511_);
lean_dec_ref(v_arg_2508_);
lean_dec_ref(v_e_2358_);
v_a_2541_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2517_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2517_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
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
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_e_2358_);
v_a_2549_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2379_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2379_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
v___jp_2370_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
v___jp_2373_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
v___jp_2376_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateEqDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2358_ = stack[0].m_obj;
lean_object* v_a_2359_ = stack[1].m_obj;
lean_object* v_a_2360_ = stack[2].m_obj;
lean_object* v_a_2361_ = stack[3].m_obj;
lean_object* v_a_2362_ = stack[4].m_obj;
lean_object* v_a_2363_ = stack[5].m_obj;
lean_object* v_a_2364_ = stack[6].m_obj;
lean_object* v_a_2365_ = stack[7].m_obj;
lean_object* v_a_2366_ = stack[8].m_obj;
lean_object* v_a_2367_ = stack[9].m_obj;
lean_object* v_a_2368_ = stack[10].m_obj;
lean_object* v_res_2557_;
v_res_2557_ = l_Lean_Meta_Grind_propagateEqDown(v_e_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
stack->m_obj
 = v_res_2557_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown___boxed(lean_object* v_e_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_Grind_propagateEqDown(v_e_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec(v_a_2559_);
return v_res_2570_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2573_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown___boxed), 12, 0);
v___x_2574_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2572_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2575_;
v_res_2575_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9____boxed(lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqDown___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2318196400____hygCtx___hyg_9_();
return v_res_2577_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(lean_object* v_u_2581_, lean_object* v_00_u03b1_2582_, lean_object* v_binst_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___closed__1));
v___x_2590_ = l_Lean_mkConst(v___x_2589_, v_u_2581_);
v___x_2591_ = l_Lean_mkAppB(v___x_2590_, v_00_u03b1_2582_, v_binst_2583_);
v___x_2592_ = lean_box(0);
v___x_2593_ = l_Lean_Meta_synthInstance_x3f(v___x_2591_, v___x_2592_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
return v___x_2593_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2581_ = stack[0].m_obj;
lean_object* v_00_u03b1_2582_ = stack[1].m_obj;
lean_object* v_binst_2583_ = stack[2].m_obj;
lean_object* v_a_2584_ = stack[3].m_obj;
lean_object* v_a_2585_ = stack[4].m_obj;
lean_object* v_a_2586_ = stack[5].m_obj;
lean_object* v_a_2587_ = stack[6].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2581_, v_00_u03b1_2582_, v_binst_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg___boxed(lean_object* v_u_2595_, lean_object* v_00_u03b1_2596_, lean_object* v_binst_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2595_, v_00_u03b1_2596_, v_binst_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
return v_res_2603_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(lean_object* v_u_2604_, lean_object* v_00_u03b1_2605_, lean_object* v_binst_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2604_, v_00_u03b1_2605_, v_binst_2606_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2604_ = stack[0].m_obj;
lean_object* v_00_u03b1_2605_ = stack[1].m_obj;
lean_object* v_binst_2606_ = stack[2].m_obj;
lean_object* v_a_2607_ = stack[3].m_obj;
lean_object* v_a_2608_ = stack[4].m_obj;
lean_object* v_a_2609_ = stack[5].m_obj;
lean_object* v_a_2610_ = stack[6].m_obj;
lean_object* v_a_2611_ = stack[7].m_obj;
lean_object* v_a_2612_ = stack[8].m_obj;
lean_object* v_a_2613_ = stack[9].m_obj;
lean_object* v_a_2614_ = stack[10].m_obj;
lean_object* v_a_2615_ = stack[11].m_obj;
lean_object* v_a_2616_ = stack[12].m_obj;
lean_object* v_res_2619_;
v_res_2619_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(v_u_2604_, v_00_u03b1_2605_, v_binst_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_);
stack->m_obj
 = v_res_2619_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___boxed(lean_object* v_u_2620_, lean_object* v_00_u03b1_2621_, lean_object* v_binst_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f(v_u_2620_, v_00_u03b1_2621_, v_binst_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec(v_a_2623_);
return v_res_2634_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* v_e_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
lean_inc_ref(v_e_2650_);
v___x_2665_ = l_Lean_Expr_cleanupAnnotations(v_e_2650_);
v___x_2666_ = l_Lean_Expr_isApp(v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v___x_2665_);
lean_dec_ref(v_e_2650_);
goto v___jp_2662_;
}
else
{
lean_object* v_arg_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_arg_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc_ref(v_arg_2667_);
v___x_2668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2665_);
v___x_2669_ = l_Lean_Expr_isApp(v___x_2668_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v___x_2668_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
goto v___jp_2662_;
}
else
{
lean_object* v_arg_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_arg_2670_ = lean_ctor_get(v___x_2668_, 1);
lean_inc_ref(v_arg_2670_);
v___x_2671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2668_);
v___x_2672_ = l_Lean_Expr_isApp(v___x_2671_);
if (v___x_2672_ == 0)
{
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
goto v___jp_2662_;
}
else
{
lean_object* v_arg_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_arg_2673_ = lean_ctor_get(v___x_2671_, 1);
lean_inc_ref(v_arg_2673_);
v___x_2674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2671_);
v___x_2675_ = l_Lean_Expr_isApp(v___x_2674_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v___x_2674_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
goto v___jp_2662_;
}
else
{
lean_object* v_arg_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_arg_2676_ = lean_ctor_get(v___x_2674_, 1);
lean_inc_ref(v_arg_2676_);
v___x_2677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2674_);
v___x_2678_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2679_ = l_Lean_Expr_isConstOf(v___x_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
goto v___jp_2662_;
}
else
{
lean_object* v_u_2680_; lean_object* v___x_2681_; 
v_u_2680_ = l_Lean_Expr_constLevels_x21(v___x_2677_);
lean_dec_ref(v___x_2677_);
v___x_2681_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_2670_, v_arg_2667_, v_a_2651_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; uint8_t v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_unbox(v_a_2682_);
lean_dec(v_a_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
lean_inc_ref(v_arg_2667_);
lean_inc_ref(v_arg_2670_);
v___x_2684_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(v_arg_2670_, v_arg_2667_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2717_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2717_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2717_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
if (lean_obj_tag(v_a_2685_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2687_);
v_val_2689_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v_a_2685_, 1);
lean_inc_ref(v_arg_2673_);
lean_inc_ref(v_arg_2676_);
lean_inc(v_u_2680_);
v___x_2690_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2680_, v_arg_2676_, v_arg_2673_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2704_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2704_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
if (lean_obj_tag(v_a_2691_) == 1)
{
lean_object* v_val_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_del_object(v___x_2693_);
v_val_2695_ = lean_ctor_get(v_a_2691_, 0);
lean_inc(v_val_2695_);
lean_dec_ref_known(v_a_2691_, 1);
v___x_2696_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__4));
v___x_2697_ = l_Lean_mkConst(v___x_2696_, v_u_2680_);
v___x_2698_ = l_Lean_mkApp6(v___x_2697_, v_arg_2676_, v_arg_2673_, v_val_2695_, v_arg_2670_, v_arg_2667_, v_val_2689_);
v___x_2699_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_2650_, v___x_2698_, v_a_2651_, v_a_2653_, v_a_2655_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2699_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v_a_2691_);
lean_dec(v_val_2689_);
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v___x_2700_ = lean_box(0);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2700_);
v___x_2702_ = v___x_2693_;
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
lean_dec(v_val_2689_);
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v_a_2705_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2690_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2690_);
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
lean_object* v___x_2713_; lean_object* v___x_2715_; 
lean_dec(v_a_2685_);
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v___x_2713_ = lean_box(0);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2713_);
v___x_2715_ = v___x_2687_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v_a_2718_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2684_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2684_);
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
lean_object* v___x_2726_; 
lean_inc_ref(v_arg_2673_);
lean_inc_ref(v_arg_2676_);
lean_inc(v_u_2680_);
v___x_2726_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2680_, v_arg_2676_, v_arg_2673_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2750_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2750_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2750_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
if (lean_obj_tag(v_a_2727_) == 1)
{
lean_object* v_val_2731_; lean_object* v___x_2732_; 
lean_del_object(v___x_2729_);
v_val_2731_ = lean_ctor_get(v_a_2727_, 0);
lean_inc(v_val_2731_);
lean_dec_ref_known(v_a_2727_, 1);
lean_inc(v_a_2660_);
lean_inc_ref(v_a_2659_);
lean_inc(v_a_2658_);
lean_inc_ref(v_a_2657_);
lean_inc(v_a_2656_);
lean_inc_ref(v_a_2655_);
lean_inc(v_a_2654_);
lean_inc_ref(v_a_2653_);
lean_inc(v_a_2652_);
lean_inc(v_a_2651_);
lean_inc_ref(v_arg_2667_);
lean_inc_ref(v_arg_2670_);
v___x_2732_ = lean_grind_mk_eq_proof(v_arg_2670_, v_arg_2667_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__6));
v___x_2735_ = l_Lean_mkConst(v___x_2734_, v_u_2680_);
v___x_2736_ = l_Lean_mkApp6(v___x_2735_, v_arg_2676_, v_arg_2673_, v_val_2731_, v_arg_2670_, v_arg_2667_, v_a_2733_);
v___x_2737_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_2650_, v___x_2736_, v_a_2651_, v_a_2653_, v_a_2655_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
return v___x_2737_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_val_2731_);
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v_a_2738_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2732_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2732_);
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
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_a_2727_);
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v___x_2746_ = lean_box(0);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2746_);
v___x_2748_ = v___x_2729_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v_a_2751_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2726_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2726_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_u_2680_);
lean_dec_ref(v_arg_2676_);
lean_dec_ref(v_arg_2673_);
lean_dec_ref(v_arg_2670_);
lean_dec_ref(v_arg_2667_);
lean_dec_ref(v_e_2650_);
v_a_2759_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2681_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2681_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
}
}
v___jp_2662_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_box(0);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBEqUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2650_ = stack[0].m_obj;
lean_object* v_a_2651_ = stack[1].m_obj;
lean_object* v_a_2652_ = stack[2].m_obj;
lean_object* v_a_2653_ = stack[3].m_obj;
lean_object* v_a_2654_ = stack[4].m_obj;
lean_object* v_a_2655_ = stack[5].m_obj;
lean_object* v_a_2656_ = stack[6].m_obj;
lean_object* v_a_2657_ = stack[7].m_obj;
lean_object* v_a_2658_ = stack[8].m_obj;
lean_object* v_a_2659_ = stack[9].m_obj;
lean_object* v_a_2660_ = stack[10].m_obj;
lean_object* v_res_2767_;
v_res_2767_ = l_Lean_Meta_Grind_propagateBEqUp(v_e_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
stack->m_obj
 = v_res_2767_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp___boxed(lean_object* v_e_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_Grind_propagateBEqUp(v_e_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec(v_a_2769_);
return v_res_2780_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2783_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp___boxed), 12, 0);
v___x_2784_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2782_, v___x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2785_;
v_res_2785_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9____boxed(lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqUp___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4192136612____hygCtx___hyg_9_();
return v_res_2787_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBEqDown(lean_object* v_e_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2813_; uint8_t v___x_2814_; 
lean_inc_ref(v_e_2798_);
v___x_2813_ = l_Lean_Expr_cleanupAnnotations(v_e_2798_);
v___x_2814_ = l_Lean_Expr_isApp(v___x_2813_);
if (v___x_2814_ == 0)
{
lean_dec_ref(v___x_2813_);
lean_dec_ref(v_e_2798_);
goto v___jp_2810_;
}
else
{
lean_object* v_arg_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_arg_2815_ = lean_ctor_get(v___x_2813_, 1);
lean_inc_ref(v_arg_2815_);
v___x_2816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2813_);
v___x_2817_ = l_Lean_Expr_isApp(v___x_2816_);
if (v___x_2817_ == 0)
{
lean_dec_ref(v___x_2816_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
goto v___jp_2810_;
}
else
{
lean_object* v_arg_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v_arg_2818_ = lean_ctor_get(v___x_2816_, 1);
lean_inc_ref(v_arg_2818_);
v___x_2819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2816_);
v___x_2820_ = l_Lean_Expr_isApp(v___x_2819_);
if (v___x_2820_ == 0)
{
lean_dec_ref(v___x_2819_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
goto v___jp_2810_;
}
else
{
lean_object* v_arg_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v_arg_2821_ = lean_ctor_get(v___x_2819_, 1);
lean_inc_ref(v_arg_2821_);
v___x_2822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2819_);
v___x_2823_ = l_Lean_Expr_isApp(v___x_2822_);
if (v___x_2823_ == 0)
{
lean_dec_ref(v___x_2822_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
goto v___jp_2810_;
}
else
{
lean_object* v_arg_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_arg_2824_ = lean_ctor_get(v___x_2822_, 1);
lean_inc_ref(v_arg_2824_);
v___x_2825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2822_);
v___x_2826_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2827_ = l_Lean_Expr_isConstOf(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec_ref(v___x_2825_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2828_; lean_object* v_u_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_box(0);
v_u_2829_ = l_Lean_Expr_constLevels_x21(v___x_2825_);
lean_dec_ref(v___x_2825_);
lean_inc_ref(v_e_2798_);
v___x_2830_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_2798_, v_a_2799_, v_a_2803_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; uint8_t v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = lean_unbox(v_a_2831_);
lean_dec(v_a_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
lean_inc_ref(v_e_2798_);
v___x_2833_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_2798_, v_a_2799_, v_a_2803_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2915_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2915_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2915_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___x_2838_; 
v___x_2838_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v___x_2839_ = lean_box(0);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
else
{
lean_object* v___x_2843_; 
lean_del_object(v___x_2836_);
lean_inc_ref(v_arg_2821_);
lean_inc_ref(v_arg_2824_);
lean_inc(v_u_2829_);
v___x_2843_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2829_, v_arg_2824_, v_arg_2821_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2906_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2906_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2906_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 1)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_del_object(v___x_2846_);
v_val_2848_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v_a_2844_, 1);
v___x_2849_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqUp___closed__1));
v___x_2850_ = l_List_head_x21___redArg(v___x_2828_, v_u_2829_);
v___x_2851_ = l_Lean_Level_succ___override(v___x_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = l_Lean_mkConst(v___x_2849_, v___x_2853_);
lean_inc_ref(v_arg_2815_);
lean_inc_ref(v_arg_2818_);
lean_inc_ref(v_arg_2824_);
v___x_2855_ = l_Lean_mkApp3(v___x_2854_, v_arg_2824_, v_arg_2818_, v_arg_2815_);
v___x_2856_ = l_Lean_Meta_Sym_shareCommon(v___x_2855_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2858_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v___x_2858_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_2818_, v_a_2799_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = lean_box(0);
lean_inc(v_a_2808_);
lean_inc_ref(v_a_2807_);
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc(v_a_2802_);
lean_inc_ref(v_a_2801_);
lean_inc(v_a_2800_);
lean_inc(v_a_2799_);
lean_inc(v_a_2857_);
v___x_2861_ = lean_grind_internalize(v_a_2857_, v_a_2859_, v___x_2860_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref_known(v___x_2861_, 1);
v___x_2862_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2803_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
lean_inc(v_a_2808_);
lean_inc_ref(v_a_2807_);
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc(v_a_2802_);
lean_inc_ref(v_a_2801_);
lean_inc(v_a_2800_);
lean_inc(v_a_2799_);
v___x_2864_ = lean_grind_mk_eq_proof(v_e_2798_, v_a_2863_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__1));
v___x_2867_ = l_Lean_mkConst(v___x_2866_, v_u_2829_);
v___x_2868_ = l_Lean_mkApp6(v___x_2867_, v_arg_2824_, v_arg_2821_, v_val_2848_, v_arg_2818_, v_arg_2815_, v_a_2865_);
v___x_2869_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_2857_, v___x_2868_, v_a_2799_, v_a_2801_, v_a_2803_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2869_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2857_);
lean_dec(v_val_2848_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
v_a_2870_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2864_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2864_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
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
lean_dec(v_a_2857_);
lean_dec(v_val_2848_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2878_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2862_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2862_);
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
else
{
lean_dec(v_a_2857_);
lean_dec(v_val_2848_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
return v___x_2861_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_a_2857_);
lean_dec(v_val_2848_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2886_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2858_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2858_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_val_2848_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2894_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2856_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2856_);
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
lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_dec(v_a_2844_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v___x_2902_ = lean_box(0);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2902_);
v___x_2904_ = v___x_2846_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2907_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2843_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2843_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2916_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2833_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2833_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v___x_2924_; 
lean_inc_ref(v_arg_2821_);
lean_inc_ref(v_arg_2824_);
lean_inc(v_u_2829_);
v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_getLawfulBEqInst_x3f___redArg(v_u_2829_, v_arg_2824_, v_arg_2821_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2959_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2959_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2959_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
if (lean_obj_tag(v_a_2925_) == 1)
{
lean_object* v_val_2929_; lean_object* v___x_2930_; 
lean_del_object(v___x_2927_);
v_val_2929_ = lean_ctor_get(v_a_2925_, 0);
lean_inc(v_val_2929_);
lean_dec_ref_known(v_a_2925_, 1);
v___x_2930_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2803_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
lean_inc(v_a_2808_);
lean_inc_ref(v_a_2807_);
lean_inc(v_a_2806_);
lean_inc_ref(v_a_2805_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc(v_a_2802_);
lean_inc_ref(v_a_2801_);
lean_inc(v_a_2800_);
lean_inc(v_a_2799_);
v___x_2932_ = lean_grind_mk_eq_proof(v_e_2798_, v_a_2931_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqDown___closed__3));
v___x_2935_ = l_Lean_mkConst(v___x_2934_, v_u_2829_);
lean_inc_ref(v_arg_2815_);
lean_inc_ref(v_arg_2818_);
v___x_2936_ = l_Lean_mkApp6(v___x_2935_, v_arg_2824_, v_arg_2821_, v_val_2929_, v_arg_2818_, v_arg_2815_, v_a_2933_);
v___x_2937_ = 0;
v___x_2938_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_2818_, v_arg_2815_, v___x_2936_, v___x_2937_, v_a_2799_, v_a_2801_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2938_;
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_val_2929_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
v_a_2939_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2932_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2932_);
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
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec(v_val_2929_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2947_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2930_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2930_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_dec(v_a_2925_);
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v___x_2955_ = lean_box(0);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2955_);
v___x_2957_ = v___x_2927_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2960_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2924_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2924_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_u_2829_);
lean_dec_ref(v_arg_2824_);
lean_dec_ref(v_arg_2821_);
lean_dec_ref(v_arg_2818_);
lean_dec_ref(v_arg_2815_);
lean_dec_ref(v_e_2798_);
v_a_2968_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2830_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2830_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
}
}
v___jp_2810_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBEqDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2798_ = stack[0].m_obj;
lean_object* v_a_2799_ = stack[1].m_obj;
lean_object* v_a_2800_ = stack[2].m_obj;
lean_object* v_a_2801_ = stack[3].m_obj;
lean_object* v_a_2802_ = stack[4].m_obj;
lean_object* v_a_2803_ = stack[5].m_obj;
lean_object* v_a_2804_ = stack[6].m_obj;
lean_object* v_a_2805_ = stack[7].m_obj;
lean_object* v_a_2806_ = stack[8].m_obj;
lean_object* v_a_2807_ = stack[9].m_obj;
lean_object* v_a_2808_ = stack[10].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_Meta_Grind_propagateBEqDown(v_e_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqDown___boxed(lean_object* v_e_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Meta_Grind_propagateBEqDown(v_e_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec(v_a_2978_);
return v_res_2989_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBEqUp___closed__2));
v___x_2992_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqDown___boxed), 12, 0);
v___x_2993_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2991_, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2994_;
v_res_2994_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2994_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9____boxed(lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBEqDown___regBuiltin_Lean_Meta_Grind_propagateBEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1906898770____hygCtx___hyg_9_();
return v_res_2996_;
}
}
lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* v_e_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3017_; 
lean_inc_ref(v_e_3002_);
v___x_3017_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3002_, v_a_3003_, v_a_3007_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3055_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3055_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3055_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_unbox(v_a_3018_);
lean_dec(v_a_3018_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec_ref(v_e_3002_);
v___x_3023_ = lean_box(0);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
else
{
lean_object* v___x_3027_; uint8_t v___x_3028_; 
lean_del_object(v___x_3020_);
lean_inc_ref(v_e_3002_);
v___x_3027_ = l_Lean_Expr_cleanupAnnotations(v_e_3002_);
v___x_3028_ = l_Lean_Expr_isApp(v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec_ref(v___x_3027_);
lean_dec_ref(v_e_3002_);
goto v___jp_3014_;
}
else
{
lean_object* v_arg_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_arg_3029_ = lean_ctor_get(v___x_3027_, 1);
lean_inc_ref(v_arg_3029_);
v___x_3030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3027_);
v___x_3031_ = l_Lean_Expr_isApp(v___x_3030_);
if (v___x_3031_ == 0)
{
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_arg_3029_);
lean_dec_ref(v_e_3002_);
goto v___jp_3014_;
}
else
{
lean_object* v_arg_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_arg_3032_ = lean_ctor_get(v___x_3030_, 1);
lean_inc_ref(v_arg_3032_);
v___x_3033_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3030_);
v___x_3034_ = l_Lean_Expr_isApp(v___x_3033_);
if (v___x_3034_ == 0)
{
lean_dec_ref(v___x_3033_);
lean_dec_ref(v_arg_3032_);
lean_dec_ref(v_arg_3029_);
lean_dec_ref(v_e_3002_);
goto v___jp_3014_;
}
else
{
lean_object* v_arg_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v_arg_3035_ = lean_ctor_get(v___x_3033_, 1);
lean_inc_ref(v_arg_3035_);
v___x_3036_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3033_);
v___x_3037_ = l_Lean_Expr_isApp(v___x_3036_);
if (v___x_3037_ == 0)
{
lean_dec_ref(v___x_3036_);
lean_dec_ref(v_arg_3035_);
lean_dec_ref(v_arg_3032_);
lean_dec_ref(v_arg_3029_);
lean_dec_ref(v_e_3002_);
goto v___jp_3014_;
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3038_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3036_);
v___x_3039_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3040_ = l_Lean_Expr_isConstOf(v___x_3038_, v___x_3039_);
lean_dec_ref(v___x_3038_);
if (v___x_3040_ == 0)
{
lean_dec_ref(v_arg_3035_);
lean_dec_ref(v_arg_3032_);
lean_dec_ref(v_arg_3029_);
lean_dec_ref(v_e_3002_);
goto v___jp_3014_;
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Meta_Grind_markCaseSplitAsResolved(v_arg_3029_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v___x_3042_; 
lean_dec_ref_known(v___x_3041_, 1);
lean_inc_ref(v_e_3002_);
v___x_3042_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3002_, v_a_3043_);
v___x_3045_ = 0;
v___x_3046_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3035_, v_arg_3032_, v___x_3044_, v___x_3045_, v_a_3003_, v_a_3005_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3046_;
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_arg_3035_);
lean_dec_ref(v_arg_3032_);
lean_dec_ref(v_e_3002_);
v_a_3047_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3042_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3042_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3035_);
lean_dec_ref(v_arg_3032_);
lean_dec_ref(v_e_3002_);
return v___x_3041_;
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
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_e_3002_);
v_a_3056_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3017_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3017_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
v___jp_3014_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateEqMatchDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3002_ = stack[0].m_obj;
lean_object* v_a_3003_ = stack[1].m_obj;
lean_object* v_a_3004_ = stack[2].m_obj;
lean_object* v_a_3005_ = stack[3].m_obj;
lean_object* v_a_3006_ = stack[4].m_obj;
lean_object* v_a_3007_ = stack[5].m_obj;
lean_object* v_a_3008_ = stack[6].m_obj;
lean_object* v_a_3009_ = stack[7].m_obj;
lean_object* v_a_3010_ = stack[8].m_obj;
lean_object* v_a_3011_ = stack[9].m_obj;
lean_object* v_a_3012_ = stack[10].m_obj;
lean_object* v_res_3064_;
v_res_3064_ = l_Lean_Meta_Grind_propagateEqMatchDown(v_e_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
stack->m_obj
 = v_res_3064_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown___boxed(lean_object* v_e_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Meta_Grind_propagateEqMatchDown(v_e_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec(v_a_3066_);
return v_res_3077_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((lean_object*)(l_Lean_Meta_Grind_propagateEqMatchDown___closed__1));
v___x_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown___boxed), 12, 0);
v___x_3081_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3079_, v___x_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3082_;
v_res_3082_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3082_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9____boxed(lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateEqMatchDown___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_4201098355____hygCtx___hyg_9_();
return v_res_3084_;
}
}
lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* v_e_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v___x_3103_; 
lean_inc_ref(v_e_3088_);
v___x_3103_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_3088_, v_a_3089_, v_a_3093_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3139_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3139_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3139_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_unbox(v_a_3104_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
v___x_3109_ = lean_box(0);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3109_);
v___x_3111_ = v___x_3106_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v___x_3113_; uint8_t v___x_3114_; 
lean_del_object(v___x_3106_);
lean_inc_ref(v_e_3088_);
v___x_3113_ = l_Lean_Expr_cleanupAnnotations(v_e_3088_);
v___x_3114_ = l_Lean_Expr_isApp(v___x_3113_);
if (v___x_3114_ == 0)
{
lean_dec_ref(v___x_3113_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
goto v___jp_3100_;
}
else
{
lean_object* v_arg_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v_arg_3115_ = lean_ctor_get(v___x_3113_, 1);
lean_inc_ref(v_arg_3115_);
v___x_3116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3113_);
v___x_3117_ = l_Lean_Expr_isApp(v___x_3116_);
if (v___x_3117_ == 0)
{
lean_dec_ref(v___x_3116_);
lean_dec_ref(v_arg_3115_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
goto v___jp_3100_;
}
else
{
lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3116_);
v___x_3119_ = l_Lean_Expr_isApp(v___x_3118_);
if (v___x_3119_ == 0)
{
lean_dec_ref(v___x_3118_);
lean_dec_ref(v_arg_3115_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
goto v___jp_3100_;
}
else
{
lean_object* v_arg_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_arg_3120_ = lean_ctor_get(v___x_3118_, 1);
lean_inc_ref(v_arg_3120_);
v___x_3121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3118_);
v___x_3122_ = l_Lean_Expr_isApp(v___x_3121_);
if (v___x_3122_ == 0)
{
lean_dec_ref(v___x_3121_);
lean_dec_ref(v_arg_3120_);
lean_dec_ref(v_arg_3115_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
goto v___jp_3100_;
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3121_);
v___x_3124_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3125_ = l_Lean_Expr_isConstOf(v___x_3123_, v___x_3124_);
lean_dec_ref(v___x_3123_);
if (v___x_3125_ == 0)
{
lean_dec_ref(v_arg_3120_);
lean_dec_ref(v_arg_3115_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
goto v___jp_3100_;
}
else
{
lean_object* v___x_3126_; 
lean_inc_ref(v_e_3088_);
v___x_3126_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3088_, v_a_3127_);
v___x_3129_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
v___x_3130_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_arg_3120_, v_arg_3115_, v___x_3128_, v___x_3129_, v_a_3089_, v_a_3091_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3130_;
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_arg_3120_);
lean_dec_ref(v_arg_3115_);
lean_dec(v_a_3104_);
lean_dec_ref(v_e_3088_);
v_a_3131_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3126_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3126_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
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
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_e_3088_);
v_a_3140_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3103_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3103_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
v___jp_3100_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
return v___x_3102_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateHEqDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3088_ = stack[0].m_obj;
lean_object* v_a_3089_ = stack[1].m_obj;
lean_object* v_a_3090_ = stack[2].m_obj;
lean_object* v_a_3091_ = stack[3].m_obj;
lean_object* v_a_3092_ = stack[4].m_obj;
lean_object* v_a_3093_ = stack[5].m_obj;
lean_object* v_a_3094_ = stack[6].m_obj;
lean_object* v_a_3095_ = stack[7].m_obj;
lean_object* v_a_3096_ = stack[8].m_obj;
lean_object* v_a_3097_ = stack[9].m_obj;
lean_object* v_a_3098_ = stack[10].m_obj;
lean_object* v_res_3148_;
v_res_3148_ = l_Lean_Meta_Grind_propagateHEqDown(v_e_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown___boxed(lean_object* v_e_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Meta_Grind_propagateHEqDown(v_e_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec(v_a_3150_);
return v_res_3161_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3163_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3164_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown___boxed), 12, 0);
v___x_3165_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3163_, v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3166_;
v_res_3166_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9____boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqDown___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_735922284____hygCtx___hyg_9_();
return v_res_3168_;
}
}
lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* v_e_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
lean_inc_ref(v_e_3169_);
v___x_3184_ = l_Lean_Expr_cleanupAnnotations(v_e_3169_);
v___x_3185_ = l_Lean_Expr_isApp(v___x_3184_);
if (v___x_3185_ == 0)
{
lean_dec_ref(v___x_3184_);
lean_dec_ref(v_e_3169_);
goto v___jp_3181_;
}
else
{
lean_object* v_arg_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v_arg_3186_ = lean_ctor_get(v___x_3184_, 1);
lean_inc_ref(v_arg_3186_);
v___x_3187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3184_);
v___x_3188_ = l_Lean_Expr_isApp(v___x_3187_);
if (v___x_3188_ == 0)
{
lean_dec_ref(v___x_3187_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3187_);
v___x_3190_ = l_Lean_Expr_isApp(v___x_3189_);
if (v___x_3190_ == 0)
{
lean_dec_ref(v___x_3189_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
goto v___jp_3181_;
}
else
{
lean_object* v_arg_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v_arg_3191_ = lean_ctor_get(v___x_3189_, 1);
lean_inc_ref(v_arg_3191_);
v___x_3192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3189_);
v___x_3193_ = l_Lean_Expr_isApp(v___x_3192_);
if (v___x_3193_ == 0)
{
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_arg_3191_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; 
v___x_3194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3192_);
v___x_3195_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3196_ = l_Lean_Expr_isConstOf(v___x_3194_, v___x_3195_);
lean_dec_ref(v___x_3194_);
if (v___x_3196_ == 0)
{
lean_dec_ref(v_arg_3191_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
goto v___jp_3181_;
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Meta_Grind_isEqv___redArg(v_arg_3191_, v_arg_3186_, v_a_3170_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3219_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3219_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3219_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
uint8_t v___x_3202_; 
v___x_3202_ = lean_unbox(v_a_3198_);
lean_dec(v_a_3198_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_dec_ref(v_arg_3191_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
v___x_3203_ = lean_box(0);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3203_);
v___x_3205_ = v___x_3200_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
else
{
lean_object* v___x_3207_; 
lean_del_object(v___x_3200_);
lean_inc(v_a_3179_);
lean_inc_ref(v_a_3178_);
lean_inc(v_a_3177_);
lean_inc_ref(v_a_3176_);
lean_inc(v_a_3175_);
lean_inc_ref(v_a_3174_);
lean_inc(v_a_3173_);
lean_inc_ref(v_a_3172_);
lean_inc(v_a_3171_);
lean_inc(v_a_3170_);
v___x_3207_ = lean_grind_mk_heq_proof(v_arg_3191_, v_arg_3186_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
lean_inc_ref(v_e_3169_);
v___x_3209_ = l_Lean_Meta_mkEqTrueCore(v_e_3169_, v_a_3208_);
v___x_3210_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_3169_, v___x_3209_, v_a_3170_, v_a_3172_, v_a_3174_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
return v___x_3210_;
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v_e_3169_);
v_a_3211_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3207_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3207_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v_arg_3191_);
lean_dec_ref(v_arg_3186_);
lean_dec_ref(v_e_3169_);
v_a_3220_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3197_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3197_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
}
}
}
v___jp_3181_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateHEqUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3169_ = stack[0].m_obj;
lean_object* v_a_3170_ = stack[1].m_obj;
lean_object* v_a_3171_ = stack[2].m_obj;
lean_object* v_a_3172_ = stack[3].m_obj;
lean_object* v_a_3173_ = stack[4].m_obj;
lean_object* v_a_3174_ = stack[5].m_obj;
lean_object* v_a_3175_ = stack[6].m_obj;
lean_object* v_a_3176_ = stack[7].m_obj;
lean_object* v_a_3177_ = stack[8].m_obj;
lean_object* v_a_3178_ = stack[9].m_obj;
lean_object* v_a_3179_ = stack[10].m_obj;
lean_object* v_res_3228_;
v_res_3228_ = l_Lean_Meta_Grind_propagateHEqUp(v_e_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
stack->m_obj
 = v_res_3228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp___boxed(lean_object* v_e_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Meta_Grind_propagateHEqUp(v_e_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec(v_a_3230_);
return v_res_3241_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((lean_object*)(l_Lean_Meta_Grind_propagateHEqDown___closed__1));
v___x_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp___boxed), 12, 0);
v___x_3245_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3243_, v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3246_;
v_res_3246_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3246_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9____boxed(lean_object* v_a_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateHEqUp___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3328109199____hygCtx___hyg_9_();
return v_res_3248_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(lean_object* v_e_3249_, lean_object* v_args_3250_, uint8_t v_ite_3251_, lean_object* v_rhs_3252_, lean_object* v_h_3253_, lean_object* v_i_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_array_get_size(v_args_3250_);
v___x_3267_ = lean_nat_dec_lt(v_i_3254_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec(v_i_3254_);
v___x_3268_ = l_Lean_Meta_Grind_preprocessLight___redArg(v_rhs_3252_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3249_, v_a_3255_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
lean_inc_ref(v_e_3249_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_e_3249_);
lean_inc(v_a_3264_);
lean_inc_ref(v_a_3263_);
lean_inc(v_a_3262_);
lean_inc_ref(v_a_3261_);
lean_inc(v_a_3260_);
lean_inc_ref(v_a_3259_);
lean_inc(v_a_3258_);
lean_inc_ref(v_a_3257_);
lean_inc(v_a_3256_);
lean_inc(v_a_3255_);
lean_inc(v_a_3269_);
v___x_3273_ = lean_grind_internalize(v_a_3269_, v_a_3271_, v___x_3272_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_dec_ref_known(v___x_3273_, 1);
if (v_ite_3251_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3249_, v_a_3269_, v_h_3253_, v___x_3267_, v_a_3255_, v_a_3257_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; 
lean_inc(v_a_3269_);
lean_inc_ref(v_e_3249_);
v___x_3275_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3249_, v_a_3269_, v_a_3255_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3276_; 
lean_dec_ref_known(v___x_3275_, 1);
v___x_3276_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3249_, v_a_3269_, v_h_3253_, v___x_3267_, v_a_3255_, v_a_3257_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
return v___x_3276_;
}
else
{
lean_dec(v_a_3269_);
lean_dec_ref(v_h_3253_);
lean_dec_ref(v_e_3249_);
return v___x_3275_;
}
}
}
else
{
lean_dec(v_a_3269_);
lean_dec_ref(v_h_3253_);
lean_dec_ref(v_e_3249_);
return v___x_3273_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_a_3269_);
lean_dec_ref(v_h_3253_);
lean_dec_ref(v_e_3249_);
v_a_3277_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3270_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3270_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v_h_3253_);
lean_dec_ref(v_e_3249_);
v_a_3285_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3268_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3268_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_arg_3293_; lean_object* v_rhs_x27_3294_; lean_object* v___x_3295_; 
v_arg_3293_ = lean_array_fget_borrowed(v_args_3250_, v_i_3254_);
lean_inc_n(v_arg_3293_, 2);
v_rhs_x27_3294_ = l_Lean_Expr_app___override(v_rhs_3252_, v_arg_3293_);
v___x_3295_ = l_Lean_Meta_mkCongrFun(v_h_3253_, v_arg_3293_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3295_, 1);
v___x_3297_ = lean_unsigned_to_nat(1u);
v___x_3298_ = lean_nat_add(v_i_3254_, v___x_3297_);
lean_dec(v_i_3254_);
v_rhs_3252_ = v_rhs_x27_3294_;
v_h_3253_ = v_a_3296_;
v_i_3254_ = v___x_3298_;
goto _start;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v_rhs_x27_3294_);
lean_dec(v_i_3254_);
lean_dec_ref(v_e_3249_);
v_a_3300_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3295_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3295_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3249_ = stack[0].m_obj;
lean_object* v_args_3250_ = stack[1].m_obj;
uint8_t v_ite_3251_ = stack[2].m_num;
lean_object* v_rhs_3252_ = stack[3].m_obj;
lean_object* v_h_3253_ = stack[4].m_obj;
lean_object* v_i_3254_ = stack[5].m_obj;
lean_object* v_a_3255_ = stack[6].m_obj;
lean_object* v_a_3256_ = stack[7].m_obj;
lean_object* v_a_3257_ = stack[8].m_obj;
lean_object* v_a_3258_ = stack[9].m_obj;
lean_object* v_a_3259_ = stack[10].m_obj;
lean_object* v_a_3260_ = stack[11].m_obj;
lean_object* v_a_3261_ = stack[12].m_obj;
lean_object* v_a_3262_ = stack[13].m_obj;
lean_object* v_a_3263_ = stack[14].m_obj;
lean_object* v_a_3264_ = stack[15].m_obj;
lean_object* v_res_3308_;
v_res_3308_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3249_, v_args_3250_, v_ite_3251_, v_rhs_3252_, v_h_3253_, v_i_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
stack->m_obj
 = v_res_3308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go___boxed(lean_object** _args){
lean_object* v_e_3309_ = _args[0];
lean_object* v_args_3310_ = _args[1];
lean_object* v_ite_3311_ = _args[2];
lean_object* v_rhs_3312_ = _args[3];
lean_object* v_h_3313_ = _args[4];
lean_object* v_i_3314_ = _args[5];
lean_object* v_a_3315_ = _args[6];
lean_object* v_a_3316_ = _args[7];
lean_object* v_a_3317_ = _args[8];
lean_object* v_a_3318_ = _args[9];
lean_object* v_a_3319_ = _args[10];
lean_object* v_a_3320_ = _args[11];
lean_object* v_a_3321_ = _args[12];
lean_object* v_a_3322_ = _args[13];
lean_object* v_a_3323_ = _args[14];
lean_object* v_a_3324_ = _args[15];
lean_object* v_a_3325_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3326_; lean_object* v_res_3327_; 
v_ite_boxed_3326_ = lean_unbox(v_ite_3311_);
v_res_3327_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3309_, v_args_3310_, v_ite_boxed_3326_, v_rhs_3312_, v_h_3313_, v_i_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec_ref(v_args_3310_);
return v_res_3327_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(lean_object* v_e_3328_, lean_object* v_rhs_3329_, lean_object* v_h_3330_, lean_object* v_prefixSize_3331_, lean_object* v_args_3332_, uint8_t v_ite_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3354_ = lean_array_get_size(v_args_3332_);
v___x_3355_ = lean_nat_dec_eq(v_prefixSize_3331_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_go(v_e_3328_, v_args_3332_, v_ite_3333_, v_rhs_3329_, v_h_3330_, v_prefixSize_3331_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; 
lean_dec(v_prefixSize_3331_);
v___x_3357_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3328_, v_a_3334_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
lean_inc_ref(v_e_3328_);
v___x_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3359_, 0, v_e_3328_);
lean_inc(v_a_3343_);
lean_inc_ref(v_a_3342_);
lean_inc(v_a_3341_);
lean_inc_ref(v_a_3340_);
lean_inc(v_a_3339_);
lean_inc_ref(v_a_3338_);
lean_inc(v_a_3337_);
lean_inc_ref(v_a_3336_);
lean_inc(v_a_3335_);
lean_inc(v_a_3334_);
lean_inc_ref(v_rhs_3329_);
v___x_3360_ = lean_grind_internalize(v_rhs_3329_, v_a_3358_, v___x_3359_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec_ref_known(v___x_3360_, 1);
if (v_ite_3333_ == 0)
{
v___y_3346_ = v_a_3334_;
v___y_3347_ = v_a_3336_;
v___y_3348_ = v_a_3340_;
v___y_3349_ = v_a_3341_;
v___y_3350_ = v_a_3342_;
v___y_3351_ = v_a_3343_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3361_; 
lean_inc_ref(v_rhs_3329_);
lean_inc_ref(v_e_3328_);
v___x_3361_ = l_Lean_Meta_Grind_registerParent___redArg(v_e_3328_, v_rhs_3329_, v_a_3334_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_dec_ref_known(v___x_3361_, 1);
v___y_3346_ = v_a_3334_;
v___y_3347_ = v_a_3336_;
v___y_3348_ = v_a_3340_;
v___y_3349_ = v_a_3341_;
v___y_3350_ = v_a_3342_;
v___y_3351_ = v_a_3343_;
goto v___jp_3345_;
}
else
{
lean_dec_ref(v_h_3330_);
lean_dec_ref(v_rhs_3329_);
lean_dec_ref(v_e_3328_);
return v___x_3361_;
}
}
}
else
{
lean_dec_ref(v_h_3330_);
lean_dec_ref(v_rhs_3329_);
lean_dec_ref(v_e_3328_);
return v___x_3360_;
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v_h_3330_);
lean_dec_ref(v_rhs_3329_);
lean_dec_ref(v_e_3328_);
v_a_3362_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3357_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3357_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
v___jp_3345_:
{
uint8_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = 0;
v___x_3353_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3328_, v_rhs_3329_, v_h_3330_, v___x_3352_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3353_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3328_ = stack[0].m_obj;
lean_object* v_rhs_3329_ = stack[1].m_obj;
lean_object* v_h_3330_ = stack[2].m_obj;
lean_object* v_prefixSize_3331_ = stack[3].m_obj;
lean_object* v_args_3332_ = stack[4].m_obj;
uint8_t v_ite_3333_ = stack[5].m_num;
lean_object* v_a_3334_ = stack[6].m_obj;
lean_object* v_a_3335_ = stack[7].m_obj;
lean_object* v_a_3336_ = stack[8].m_obj;
lean_object* v_a_3337_ = stack[9].m_obj;
lean_object* v_a_3338_ = stack[10].m_obj;
lean_object* v_a_3339_ = stack[11].m_obj;
lean_object* v_a_3340_ = stack[12].m_obj;
lean_object* v_a_3341_ = stack[13].m_obj;
lean_object* v_a_3342_ = stack[14].m_obj;
lean_object* v_a_3343_ = stack[15].m_obj;
lean_object* v_res_3370_;
v_res_3370_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3328_, v_rhs_3329_, v_h_3330_, v_prefixSize_3331_, v_args_3332_, v_ite_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
stack->m_obj
 = v_res_3370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun___boxed(lean_object** _args){
lean_object* v_e_3371_ = _args[0];
lean_object* v_rhs_3372_ = _args[1];
lean_object* v_h_3373_ = _args[2];
lean_object* v_prefixSize_3374_ = _args[3];
lean_object* v_args_3375_ = _args[4];
lean_object* v_ite_3376_ = _args[5];
lean_object* v_a_3377_ = _args[6];
lean_object* v_a_3378_ = _args[7];
lean_object* v_a_3379_ = _args[8];
lean_object* v_a_3380_ = _args[9];
lean_object* v_a_3381_ = _args[10];
lean_object* v_a_3382_ = _args[11];
lean_object* v_a_3383_ = _args[12];
lean_object* v_a_3384_ = _args[13];
lean_object* v_a_3385_ = _args[14];
lean_object* v_a_3386_ = _args[15];
lean_object* v_a_3387_ = _args[16];
_start:
{
uint8_t v_ite_boxed_3388_; lean_object* v_res_3389_; 
v_ite_boxed_3388_ = lean_unbox(v_ite_3376_);
v_res_3389_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3371_, v_rhs_3372_, v_h_3373_, v_prefixSize_3374_, v_args_3375_, v_ite_boxed_3388_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_args_3375_);
return v_res_3389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateIte___closed__0(void){
_start:
{
lean_object* v___x_3390_; lean_object* v_dummy_3391_; 
v___x_3390_ = lean_box(0);
v_dummy_3391_ = l_Lean_Expr_sort___override(v___x_3390_);
return v_dummy_3391_;
}
}
lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_numArgs_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_numArgs_3410_ = l_Lean_Expr_getAppNumArgs(v_e_3398_);
v___x_3411_ = lean_unsigned_to_nat(5u);
v___x_3412_ = lean_nat_dec_lt(v_numArgs_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v_c_3417_; lean_object* v___x_3418_; 
v___x_3413_ = l_Lean_instInhabitedExpr;
v___x_3414_ = lean_unsigned_to_nat(1u);
v___x_3415_ = lean_nat_sub(v_numArgs_3410_, v___x_3414_);
v___x_3416_ = lean_nat_sub(v___x_3415_, v___x_3414_);
v_c_3417_ = l_Lean_Expr_getRevArg_x21(v_e_3398_, v___x_3416_);
lean_inc_ref(v_c_3417_);
v___x_3418_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3417_, v_a_3399_, v_a_3403_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; uint8_t v___x_3420_; uint8_t v___x_3421_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = 1;
v___x_3421_ = lean_unbox(v_a_3419_);
lean_dec(v_a_3419_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_inc_ref(v_c_3417_);
v___x_3422_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3417_, v_a_3399_, v_a_3403_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3455_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3455_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3455_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_unbox(v_a_3423_);
lean_dec(v_a_3423_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3430_; 
lean_dec_ref(v_c_3417_);
lean_dec(v___x_3415_);
lean_dec(v_numArgs_3410_);
lean_dec_ref(v_e_3398_);
v___x_3428_ = lean_box(0);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
lean_object* v___x_3432_; lean_object* v_dummy_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_del_object(v___x_3425_);
v___x_3432_ = l_Lean_Expr_getAppFn(v_e_3398_);
v_dummy_3433_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3434_ = lean_mk_array(v_numArgs_3410_, v_dummy_3433_);
lean_inc_ref(v_e_3398_);
v___x_3435_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3398_, v___x_3434_, v___x_3415_);
v___x_3436_ = lean_unsigned_to_nat(4u);
v___x_3437_ = lean_array_get(v___x_3413_, v___x_3435_, v___x_3436_);
v___x_3438_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3417_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__2));
v___x_3441_ = l_Lean_Expr_constLevels_x21(v___x_3432_);
lean_dec_ref(v___x_3432_);
v___x_3442_ = l_Lean_mkConst(v___x_3440_, v___x_3441_);
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = l_Lean_mkAppRange(v___x_3442_, v___x_3443_, v___x_3411_, v___x_3435_);
v___x_3445_ = l_Lean_Expr_app___override(v___x_3444_, v_a_3439_);
v___x_3446_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3398_, v___x_3437_, v___x_3445_, v___x_3411_, v___x_3435_, v___x_3420_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v___x_3435_);
return v___x_3446_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___x_3437_);
lean_dec_ref(v___x_3435_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_e_3398_);
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
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v_c_3417_);
lean_dec(v___x_3415_);
lean_dec(v_numArgs_3410_);
lean_dec_ref(v_e_3398_);
v_a_3456_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3422_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3422_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v___x_3464_; lean_object* v_dummy_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3464_ = l_Lean_Expr_getAppFn(v_e_3398_);
v_dummy_3465_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3466_ = lean_mk_array(v_numArgs_3410_, v_dummy_3465_);
lean_inc_ref(v_e_3398_);
v___x_3467_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3398_, v___x_3466_, v___x_3415_);
v___x_3468_ = lean_unsigned_to_nat(3u);
v___x_3469_ = lean_array_get(v___x_3413_, v___x_3467_, v___x_3468_);
v___x_3470_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3417_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___x_3472_ = ((lean_object*)(l_Lean_Meta_Grind_propagateIte___closed__4));
v___x_3473_ = l_Lean_Expr_constLevels_x21(v___x_3464_);
lean_dec_ref(v___x_3464_);
v___x_3474_ = l_Lean_mkConst(v___x_3472_, v___x_3473_);
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = l_Lean_mkAppRange(v___x_3474_, v___x_3475_, v___x_3411_, v___x_3467_);
v___x_3477_ = l_Lean_Expr_app___override(v___x_3476_, v_a_3471_);
v___x_3478_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3398_, v___x_3469_, v___x_3477_, v___x_3411_, v___x_3467_, v___x_3420_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v___x_3467_);
return v___x_3478_;
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v___x_3469_);
lean_dec_ref(v___x_3467_);
lean_dec_ref(v___x_3464_);
lean_dec_ref(v_e_3398_);
v_a_3479_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3470_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3470_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v_c_3417_);
lean_dec(v___x_3415_);
lean_dec(v_numArgs_3410_);
lean_dec_ref(v_e_3398_);
v_a_3487_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3418_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3418_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v_numArgs_3410_);
lean_dec_ref(v_e_3398_);
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
return v___x_3496_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3398_ = stack[0].m_obj;
lean_object* v_a_3399_ = stack[1].m_obj;
lean_object* v_a_3400_ = stack[2].m_obj;
lean_object* v_a_3401_ = stack[3].m_obj;
lean_object* v_a_3402_ = stack[4].m_obj;
lean_object* v_a_3403_ = stack[5].m_obj;
lean_object* v_a_3404_ = stack[6].m_obj;
lean_object* v_a_3405_ = stack[7].m_obj;
lean_object* v_a_3406_ = stack[8].m_obj;
lean_object* v_a_3407_ = stack[9].m_obj;
lean_object* v_a_3408_ = stack[10].m_obj;
lean_object* v_res_3497_;
v_res_3497_ = l_Lean_Meta_Grind_propagateIte(v_e_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
stack->m_obj
 = v_res_3497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte___boxed(lean_object* v_e_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_Meta_Grind_propagateIte(v_e_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec(v_a_3499_);
return v_res_3510_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_));
v___x_3516_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte___boxed), 12, 0);
v___x_3517_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3515_, v___x_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3518_;
v_res_3518_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3518_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9____boxed(lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateIte___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1491137477____hygCtx___hyg_9_();
return v_res_3520_;
}
}
lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* v_e_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_numArgs_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_numArgs_3543_ = l_Lean_Expr_getAppNumArgs(v_e_3531_);
v___x_3544_ = lean_unsigned_to_nat(5u);
v___x_3545_ = lean_nat_dec_lt(v_numArgs_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v_c_3550_; lean_object* v___x_3551_; 
v___x_3546_ = l_Lean_instInhabitedExpr;
v___x_3547_ = lean_unsigned_to_nat(1u);
v___x_3548_ = lean_nat_sub(v_numArgs_3543_, v___x_3547_);
v___x_3549_ = lean_nat_sub(v___x_3548_, v___x_3547_);
v_c_3550_ = l_Lean_Expr_getRevArg_x21(v_e_3531_, v___x_3549_);
lean_inc_ref(v_c_3550_);
v___x_3551_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_c_3550_, v_a_3532_, v_a_3536_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; uint8_t v___x_3553_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = lean_unbox(v_a_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_inc_ref(v_c_3550_);
v___x_3554_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_c_3550_, v_a_3532_, v_a_3536_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3611_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3611_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3611_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
uint8_t v___x_3559_; 
v___x_3559_ = lean_unbox(v_a_3555_);
lean_dec(v_a_3555_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3562_; 
lean_dec(v_a_3552_);
lean_dec_ref(v_c_3550_);
lean_dec(v___x_3548_);
lean_dec(v_numArgs_3543_);
lean_dec_ref(v_e_3531_);
v___x_3560_ = lean_box(0);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3560_);
v___x_3562_ = v___x_3557_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
else
{
lean_object* v___x_3564_; lean_object* v_dummy_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_del_object(v___x_3557_);
v___x_3564_ = l_Lean_Expr_getAppFn(v_e_3531_);
v_dummy_3565_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3566_ = lean_mk_array(v_numArgs_3543_, v_dummy_3565_);
lean_inc_ref(v_e_3531_);
v___x_3567_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3531_, v___x_3566_, v___x_3548_);
lean_inc_ref(v_c_3550_);
v___x_3568_ = l_Lean_Meta_Grind_mkEqFalseProof(v_c_3550_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc_n(v_a_3569_, 2);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = lean_unsigned_to_nat(4u);
v___x_3571_ = lean_array_get_borrowed(v___x_3546_, v___x_3567_, v___x_3570_);
v___x_3572_ = l_Lean_Meta_mkOfEqFalseCore(v_c_3550_, v_a_3569_);
lean_inc(v___x_3571_);
v___x_3573_ = l_Lean_Expr_app___override(v___x_3571_, v___x_3572_);
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc_ref(v_a_3536_);
lean_inc(v_a_3535_);
lean_inc_ref(v_a_3534_);
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
v___x_3574_ = lean_grind_preprocess(v___x_3573_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v_expr_3576_; lean_object* v___x_3577_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v_expr_3576_ = lean_ctor_get(v_a_3575_, 0);
lean_inc_ref(v_expr_3576_);
v___x_3577_ = l_Lean_Meta_Simp_Result_getProof(v_a_3575_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; lean_object* v___x_3586_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__1));
v___x_3580_ = l_Lean_Expr_constLevels_x21(v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3581_ = l_Lean_mkConst(v___x_3579_, v___x_3580_);
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = l_Lean_mkAppRange(v___x_3581_, v___x_3582_, v___x_3544_, v___x_3567_);
lean_inc_ref(v_expr_3576_);
v___x_3584_ = l_Lean_mkApp3(v___x_3583_, v_expr_3576_, v_a_3569_, v_a_3578_);
v___x_3585_ = lean_unbox(v_a_3552_);
lean_dec(v_a_3552_);
v___x_3586_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3531_, v_expr_3576_, v___x_3584_, v___x_3544_, v___x_3567_, v___x_3585_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec_ref(v___x_3567_);
return v___x_3586_;
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v_expr_3576_);
lean_dec(v_a_3569_);
lean_dec_ref(v___x_3567_);
lean_dec_ref(v___x_3564_);
lean_dec(v_a_3552_);
lean_dec_ref(v_e_3531_);
v_a_3587_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3577_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3577_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_a_3569_);
lean_dec_ref(v___x_3567_);
lean_dec_ref(v___x_3564_);
lean_dec(v_a_3552_);
lean_dec_ref(v_e_3531_);
v_a_3595_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3574_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3574_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v___x_3567_);
lean_dec_ref(v___x_3564_);
lean_dec(v_a_3552_);
lean_dec_ref(v_c_3550_);
lean_dec_ref(v_e_3531_);
v_a_3603_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3568_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3568_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_a_3552_);
lean_dec_ref(v_c_3550_);
lean_dec(v___x_3548_);
lean_dec(v_numArgs_3543_);
lean_dec_ref(v_e_3531_);
v_a_3612_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3554_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3554_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v___x_3620_; lean_object* v_dummy_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_dec(v_a_3552_);
v___x_3620_ = l_Lean_Expr_getAppFn(v_e_3531_);
v_dummy_3621_ = lean_obj_once(&l_Lean_Meta_Grind_propagateIte___closed__0, &l_Lean_Meta_Grind_propagateIte___closed__0_once, _init_l_Lean_Meta_Grind_propagateIte___closed__0);
v___x_3622_ = lean_mk_array(v_numArgs_3543_, v_dummy_3621_);
lean_inc_ref(v_e_3531_);
v___x_3623_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3531_, v___x_3622_, v___x_3548_);
lean_inc_ref(v_c_3550_);
v___x_3624_ = l_Lean_Meta_Grind_mkEqTrueProof(v_c_3550_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc_n(v_a_3625_, 2);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = lean_unsigned_to_nat(3u);
v___x_3627_ = lean_array_get_borrowed(v___x_3546_, v___x_3623_, v___x_3626_);
v___x_3628_ = l_Lean_Meta_mkOfEqTrueCore(v_c_3550_, v_a_3625_);
lean_inc(v___x_3627_);
v___x_3629_ = l_Lean_Expr_app___override(v___x_3627_, v___x_3628_);
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc_ref(v_a_3536_);
lean_inc(v_a_3535_);
lean_inc_ref(v_a_3534_);
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
v___x_3630_ = lean_grind_preprocess(v___x_3629_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_expr_3632_; lean_object* v___x_3633_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_expr_3632_ = lean_ctor_get(v_a_3631_, 0);
lean_inc_ref(v_expr_3632_);
v___x_3633_ = l_Lean_Meta_Simp_Result_getProof(v_a_3631_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDIte___closed__3));
v___x_3636_ = l_Lean_Expr_constLevels_x21(v___x_3620_);
lean_dec_ref(v___x_3620_);
v___x_3637_ = l_Lean_mkConst(v___x_3635_, v___x_3636_);
v___x_3638_ = lean_unsigned_to_nat(0u);
v___x_3639_ = l_Lean_mkAppRange(v___x_3637_, v___x_3638_, v___x_3544_, v___x_3623_);
lean_inc_ref(v_expr_3632_);
v___x_3640_ = l_Lean_mkApp3(v___x_3639_, v_expr_3632_, v_a_3625_, v_a_3634_);
v___x_3641_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_applyCongrFun(v_e_3531_, v_expr_3632_, v___x_3640_, v___x_3544_, v___x_3623_, v___x_3545_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec_ref(v___x_3623_);
return v___x_3641_;
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_expr_3632_);
lean_dec(v_a_3625_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3620_);
lean_dec_ref(v_e_3531_);
v_a_3642_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3633_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3633_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v_a_3625_);
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3620_);
lean_dec_ref(v_e_3531_);
v_a_3650_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3630_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3630_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v___x_3623_);
lean_dec_ref(v___x_3620_);
lean_dec_ref(v_c_3550_);
lean_dec_ref(v_e_3531_);
v_a_3658_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3624_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3624_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec_ref(v_c_3550_);
lean_dec(v___x_3548_);
lean_dec(v_numArgs_3543_);
lean_dec_ref(v_e_3531_);
v_a_3666_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3551_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3551_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v_numArgs_3543_);
lean_dec_ref(v_e_3531_);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3531_ = stack[0].m_obj;
lean_object* v_a_3532_ = stack[1].m_obj;
lean_object* v_a_3533_ = stack[2].m_obj;
lean_object* v_a_3534_ = stack[3].m_obj;
lean_object* v_a_3535_ = stack[4].m_obj;
lean_object* v_a_3536_ = stack[5].m_obj;
lean_object* v_a_3537_ = stack[6].m_obj;
lean_object* v_a_3538_ = stack[7].m_obj;
lean_object* v_a_3539_ = stack[8].m_obj;
lean_object* v_a_3540_ = stack[9].m_obj;
lean_object* v_a_3541_ = stack[10].m_obj;
lean_object* v_res_3676_;
v_res_3676_ = l_Lean_Meta_Grind_propagateDIte(v_e_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
stack->m_obj
 = v_res_3676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte___boxed(lean_object* v_e_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Meta_Grind_propagateDIte(v_e_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec(v_a_3678_);
return v_res_3689_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_));
v___x_3695_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte___boxed), 12, 0);
v___x_3696_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3694_, v___x_3695_);
return v___x_3696_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3697_;
v_res_3697_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3697_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9____boxed(lean_object* v_a_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDIte___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3737351488____hygCtx___hyg_9_();
return v_res_3699_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_box(0);
v___x_3719_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__8));
v___x_3720_ = l_Lean_mkConst(v___x_3719_, v___x_3718_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__11));
v___x_3728_ = l_Lean_mkConst(v___x_3727_, v___x_3726_);
return v___x_3728_;
}
}
lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* v_e_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v___x_3744_; 
lean_inc_ref(v_e_3729_);
v___x_3744_ = l_Lean_Meta_Grind_getRootENode___redArg(v_e_3729_, v_a_3730_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3798_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3798_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3798_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
uint8_t v_ctor_3749_; 
v_ctor_3749_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*12 + 2);
if (v_ctor_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
lean_dec(v_a_3745_);
lean_dec_ref(v_e_3729_);
v___x_3750_ = lean_box(0);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3750_);
v___x_3752_ = v___x_3747_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
else
{
lean_object* v_self_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v_self_3754_ = lean_ctor_get(v_a_3745_, 0);
lean_inc_ref(v_self_3754_);
lean_dec(v_a_3745_);
lean_inc_ref(v_e_3729_);
v___x_3755_ = l_Lean_Expr_cleanupAnnotations(v_e_3729_);
v___x_3756_ = l_Lean_Expr_isApp(v___x_3755_);
if (v___x_3756_ == 0)
{
lean_dec_ref(v___x_3755_);
lean_dec_ref(v_self_3754_);
lean_del_object(v___x_3747_);
lean_dec_ref(v_e_3729_);
goto v___jp_3741_;
}
else
{
lean_object* v_arg_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_arg_3757_ = lean_ctor_get(v___x_3755_, 1);
lean_inc_ref(v_arg_3757_);
v___x_3758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3755_);
v___x_3759_ = l_Lean_Expr_isApp(v___x_3758_);
if (v___x_3759_ == 0)
{
lean_dec_ref(v___x_3758_);
lean_dec_ref(v_arg_3757_);
lean_dec_ref(v_self_3754_);
lean_del_object(v___x_3747_);
lean_dec_ref(v_e_3729_);
goto v___jp_3741_;
}
else
{
lean_object* v_arg_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v_arg_3760_ = lean_ctor_get(v___x_3758_, 1);
lean_inc_ref(v_arg_3760_);
v___x_3761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3758_);
v___x_3762_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3763_ = l_Lean_Expr_isConstOf(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3761_);
if (v___x_3763_ == 0)
{
lean_dec_ref(v_arg_3760_);
lean_dec_ref(v_arg_3757_);
lean_dec_ref(v_self_3754_);
lean_del_object(v___x_3747_);
lean_dec_ref(v_e_3729_);
goto v___jp_3741_;
}
else
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__4));
v___x_3765_ = l_Lean_Expr_isConstOf(v_self_3754_, v___x_3764_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___x_3766_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__6));
v___x_3767_ = l_Lean_Expr_isConstOf(v_self_3754_, v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_dec_ref(v_arg_3760_);
lean_dec_ref(v_arg_3757_);
lean_dec_ref(v_self_3754_);
lean_dec_ref(v_e_3729_);
v___x_3768_ = lean_box(0);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3768_);
v___x_3770_ = v___x_3747_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v___x_3772_; 
lean_del_object(v___x_3747_);
lean_inc(v_a_3739_);
lean_inc_ref(v_a_3738_);
lean_inc(v_a_3737_);
lean_inc_ref(v_a_3736_);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
lean_inc(v_a_3731_);
lean_inc(v_a_3730_);
v___x_3772_ = lean_grind_mk_eq_proof(v_e_3729_, v_self_3754_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___x_3774_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__9, &l_Lean_Meta_Grind_propagateDecideDown___closed__9_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__9);
lean_inc_ref(v_arg_3760_);
v___x_3775_ = l_Lean_mkApp3(v___x_3774_, v_arg_3760_, v_arg_3757_, v_a_3773_);
v___x_3776_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_arg_3760_, v___x_3775_, v_a_3730_, v_a_3732_, v_a_3734_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
return v___x_3776_;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_arg_3760_);
lean_dec_ref(v_arg_3757_);
v_a_3777_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3772_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3772_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
lean_object* v___x_3785_; 
lean_del_object(v___x_3747_);
lean_inc(v_a_3739_);
lean_inc_ref(v_a_3738_);
lean_inc(v_a_3737_);
lean_inc_ref(v_a_3736_);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3733_);
lean_inc_ref(v_a_3732_);
lean_inc(v_a_3731_);
lean_inc(v_a_3730_);
v___x_3785_ = lean_grind_mk_eq_proof(v_e_3729_, v_self_3754_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideDown___closed__12, &l_Lean_Meta_Grind_propagateDecideDown___closed__12_once, _init_l_Lean_Meta_Grind_propagateDecideDown___closed__12);
lean_inc_ref(v_arg_3760_);
v___x_3788_ = l_Lean_mkApp3(v___x_3787_, v_arg_3760_, v_arg_3757_, v_a_3786_);
v___x_3789_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_arg_3760_, v___x_3788_, v_a_3730_, v_a_3732_, v_a_3734_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
return v___x_3789_;
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v_arg_3760_);
lean_dec_ref(v_arg_3757_);
v_a_3790_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3785_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3785_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
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
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_e_3729_);
v_a_3799_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3744_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3744_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
v___jp_3741_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_box(0);
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateDecideDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3729_ = stack[0].m_obj;
lean_object* v_a_3730_ = stack[1].m_obj;
lean_object* v_a_3731_ = stack[2].m_obj;
lean_object* v_a_3732_ = stack[3].m_obj;
lean_object* v_a_3733_ = stack[4].m_obj;
lean_object* v_a_3734_ = stack[5].m_obj;
lean_object* v_a_3735_ = stack[6].m_obj;
lean_object* v_a_3736_ = stack[7].m_obj;
lean_object* v_a_3737_ = stack[8].m_obj;
lean_object* v_a_3738_ = stack[9].m_obj;
lean_object* v_a_3739_ = stack[10].m_obj;
lean_object* v_res_3807_;
v_res_3807_ = l_Lean_Meta_Grind_propagateDecideDown(v_e_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
stack->m_obj
 = v_res_3807_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown___boxed(lean_object* v_e_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Meta_Grind_propagateDecideDown(v_e_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec_ref(v_a_3813_);
lean_dec(v_a_3812_);
lean_dec_ref(v_a_3811_);
lean_dec(v_a_3810_);
lean_dec(v_a_3809_);
return v_res_3820_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown___boxed), 12, 0);
v___x_3824_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_3822_, v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3825_;
v_res_3825_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3825_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9____boxed(lean_object* v_a_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideDown___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1743262609____hygCtx___hyg_9_();
return v_res_3827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = lean_box(0);
v___x_3834_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__1));
v___x_3835_ = l_Lean_mkConst(v___x_3834_, v___x_3833_);
return v___x_3835_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = lean_box(0);
v___x_3842_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideUp___closed__4));
v___x_3843_ = l_Lean_mkConst(v___x_3842_, v___x_3841_);
return v___x_3843_;
}
}
lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* v_e_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
lean_inc_ref(v_e_3844_);
v___x_3859_ = l_Lean_Expr_cleanupAnnotations(v_e_3844_);
v___x_3860_ = l_Lean_Expr_isApp(v___x_3859_);
if (v___x_3860_ == 0)
{
lean_dec_ref(v___x_3859_);
lean_dec_ref(v_e_3844_);
goto v___jp_3856_;
}
else
{
lean_object* v_arg_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_arg_3861_ = lean_ctor_get(v___x_3859_, 1);
lean_inc_ref(v_arg_3861_);
v___x_3862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3859_);
v___x_3863_ = l_Lean_Expr_isApp(v___x_3862_);
if (v___x_3863_ == 0)
{
lean_dec_ref(v___x_3862_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
goto v___jp_3856_;
}
else
{
lean_object* v_arg_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_arg_3864_ = lean_ctor_get(v___x_3862_, 1);
lean_inc_ref(v_arg_3864_);
v___x_3865_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3862_);
v___x_3866_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3867_ = l_Lean_Expr_isConstOf(v___x_3865_, v___x_3866_);
lean_dec_ref(v___x_3865_);
if (v___x_3867_ == 0)
{
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
goto v___jp_3856_;
}
else
{
lean_object* v___x_3868_; 
lean_inc_ref(v_arg_3864_);
v___x_3868_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_arg_3864_, v_a_3845_, v_a_3849_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; uint8_t v___x_3870_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3870_ = lean_unbox(v_a_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_inc_ref(v_arg_3864_);
v___x_3871_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_arg_3864_, v_a_3845_, v_a_3849_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3905_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3905_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3905_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
uint8_t v___x_3876_; 
v___x_3876_ = lean_unbox(v_a_3872_);
lean_dec(v_a_3872_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_dec(v_a_3869_);
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v___x_3877_ = lean_box(0);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3877_);
v___x_3879_ = v___x_3874_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
else
{
lean_object* v___x_3881_; 
lean_del_object(v___x_3874_);
v___x_3881_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3849_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
lean_inc_ref(v_arg_3864_);
v___x_3883_ = l_Lean_Meta_Grind_mkEqFalseProof(v_arg_3864_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__2, &l_Lean_Meta_Grind_propagateDecideUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__2);
v___x_3886_ = l_Lean_mkApp3(v___x_3885_, v_arg_3864_, v_arg_3861_, v_a_3884_);
v___x_3887_ = lean_unbox(v_a_3869_);
lean_dec(v_a_3869_);
v___x_3888_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3844_, v_a_3882_, v___x_3886_, v___x_3887_, v_a_3845_, v_a_3847_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
return v___x_3888_;
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_a_3882_);
lean_dec(v_a_3869_);
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3889_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3883_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3883_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_a_3869_);
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3897_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3881_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3881_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_a_3869_);
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3906_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3871_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3871_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v___x_3914_; 
lean_dec(v_a_3869_);
v___x_3914_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3849_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
lean_inc_ref(v_arg_3864_);
v___x_3916_ = l_Lean_Meta_Grind_mkEqTrueProof(v_arg_3864_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_obj_once(&l_Lean_Meta_Grind_propagateDecideUp___closed__5, &l_Lean_Meta_Grind_propagateDecideUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateDecideUp___closed__5);
v___x_3919_ = l_Lean_mkApp3(v___x_3918_, v_arg_3864_, v_arg_3861_, v_a_3917_);
v___x_3920_ = 0;
v___x_3921_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_3844_, v_a_3915_, v___x_3919_, v___x_3920_, v_a_3845_, v_a_3847_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v_a_3915_);
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3922_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3916_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3916_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3930_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3914_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3914_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v_arg_3864_);
lean_dec_ref(v_arg_3861_);
lean_dec_ref(v_e_3844_);
v_a_3938_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3868_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3868_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
}
v___jp_3856_:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_box(0);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
return v___x_3858_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateDecideUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3844_ = stack[0].m_obj;
lean_object* v_a_3845_ = stack[1].m_obj;
lean_object* v_a_3846_ = stack[2].m_obj;
lean_object* v_a_3847_ = stack[3].m_obj;
lean_object* v_a_3848_ = stack[4].m_obj;
lean_object* v_a_3849_ = stack[5].m_obj;
lean_object* v_a_3850_ = stack[6].m_obj;
lean_object* v_a_3851_ = stack[7].m_obj;
lean_object* v_a_3852_ = stack[8].m_obj;
lean_object* v_a_3853_ = stack[9].m_obj;
lean_object* v_a_3854_ = stack[10].m_obj;
lean_object* v_res_3946_;
v_res_3946_ = l_Lean_Meta_Grind_propagateDecideUp(v_e_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp___boxed(lean_object* v_e_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Lean_Meta_Grind_propagateDecideUp(v_e_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec(v_a_3948_);
return v_res_3959_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = ((lean_object*)(l_Lean_Meta_Grind_propagateDecideDown___closed__2));
v___x_3962_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp___boxed), 12, 0);
v___x_3963_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3961_, v___x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3964_;
v_res_3964_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3964_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9____boxed(lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateDecideUp___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1074369487____hygCtx___hyg_9_();
return v_res_3966_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__2));
v___x_3978_ = l_Lean_mkConst(v___x_3977_, v___x_3976_);
return v___x_3978_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5(void){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__4));
v___x_3986_ = l_Lean_mkConst(v___x_3985_, v___x_3984_);
return v___x_3986_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = lean_box(0);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__6));
v___x_3994_ = l_Lean_mkConst(v___x_3993_, v___x_3992_);
return v___x_3994_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_box(0);
v___x_4001_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__8));
v___x_4002_ = l_Lean_mkConst(v___x_4001_, v___x_4000_);
return v___x_4002_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v___x_4018_; uint8_t v___x_4019_; 
lean_inc_ref(v_e_4003_);
v___x_4018_ = l_Lean_Expr_cleanupAnnotations(v_e_4003_);
v___x_4019_ = l_Lean_Expr_isApp(v___x_4018_);
if (v___x_4019_ == 0)
{
lean_dec_ref(v___x_4018_);
lean_dec_ref(v_e_4003_);
goto v___jp_4015_;
}
else
{
lean_object* v_arg_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v_arg_4020_ = lean_ctor_get(v___x_4018_, 1);
lean_inc_ref(v_arg_4020_);
v___x_4021_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4018_);
v___x_4022_ = l_Lean_Expr_isApp(v___x_4021_);
if (v___x_4022_ == 0)
{
lean_dec_ref(v___x_4021_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
goto v___jp_4015_;
}
else
{
lean_object* v_arg_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; uint8_t v___x_4026_; 
v_arg_4023_ = lean_ctor_get(v___x_4021_, 1);
lean_inc_ref(v_arg_4023_);
v___x_4024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4021_);
v___x_4025_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4026_ = l_Lean_Expr_isConstOf(v___x_4024_, v___x_4025_);
lean_dec_ref(v___x_4024_);
if (v___x_4026_ == 0)
{
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
goto v___jp_4015_;
}
else
{
lean_object* v___x_4027_; 
lean_inc_ref(v_arg_4023_);
v___x_4027_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4023_, v_a_4004_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; uint8_t v___x_4029_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_unbox(v_a_4028_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_inc_ref(v_arg_4020_);
v___x_4030_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4020_, v_a_4004_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; uint8_t v___x_4032_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = lean_unbox(v_a_4031_);
lean_dec(v_a_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec(v_a_4028_);
lean_inc_ref(v_arg_4023_);
v___x_4033_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4023_, v_a_4004_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; uint8_t v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = lean_unbox(v_a_4034_);
lean_dec(v_a_4034_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
lean_inc_ref(v_arg_4020_);
v___x_4036_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4020_, v_a_4004_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4059_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4059_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4059_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
uint8_t v___x_4041_; 
v___x_4041_ = lean_unbox(v_a_4037_);
lean_dec(v_a_4037_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4044_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v___x_4042_ = lean_box(0);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4042_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
else
{
lean_object* v___x_4046_; 
lean_del_object(v___x_4039_);
lean_inc_ref(v_arg_4020_);
v___x_4046_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4020_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4046_, 1);
v___x_4048_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__3, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__3);
v___x_4049_ = l_Lean_mkApp3(v___x_4048_, v_arg_4023_, v_arg_4020_, v_a_4047_);
v___x_4050_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4003_, v___x_4049_, v_a_4004_, v_a_4006_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4050_;
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4051_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4046_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4046_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4060_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4036_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4036_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v___x_4068_; 
lean_inc_ref(v_arg_4023_);
v___x_4068_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4023_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v___x_4070_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__5, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__5);
v___x_4071_ = l_Lean_mkApp3(v___x_4070_, v_arg_4023_, v_arg_4020_, v_a_4069_);
v___x_4072_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4003_, v___x_4071_, v_a_4004_, v_a_4006_, v_a_4008_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4072_;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4073_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4068_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4068_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4081_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4033_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4033_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v___x_4089_; 
lean_inc_ref(v_arg_4020_);
v___x_4089_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4020_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; uint8_t v___x_4093_; lean_object* v___x_4094_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__7, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__7);
lean_inc_ref(v_arg_4023_);
v___x_4092_ = l_Lean_mkApp3(v___x_4091_, v_arg_4023_, v_arg_4020_, v_a_4090_);
v___x_4093_ = lean_unbox(v_a_4028_);
lean_dec(v_a_4028_);
v___x_4094_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4003_, v_arg_4023_, v___x_4092_, v___x_4093_, v_a_4004_, v_a_4006_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4094_;
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v_a_4028_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4095_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4089_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4089_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4028_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4103_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4030_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4030_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v___x_4111_; 
lean_dec(v_a_4028_);
lean_inc_ref(v_arg_4023_);
v___x_4111_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4023_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndUp___closed__9, &l_Lean_Meta_Grind_propagateBoolAndUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolAndUp___closed__9);
lean_inc_ref(v_arg_4020_);
v___x_4114_ = l_Lean_mkApp3(v___x_4113_, v_arg_4023_, v_arg_4020_, v_a_4112_);
v___x_4115_ = 0;
v___x_4116_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4003_, v_arg_4020_, v___x_4114_, v___x_4115_, v_a_4004_, v_a_4006_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
return v___x_4116_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4117_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4111_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4111_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_e_4003_);
v_a_4125_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4027_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4027_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
}
v___jp_4015_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_box(0);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolAndUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4003_ = stack[0].m_obj;
lean_object* v_a_4004_ = stack[1].m_obj;
lean_object* v_a_4005_ = stack[2].m_obj;
lean_object* v_a_4006_ = stack[3].m_obj;
lean_object* v_a_4007_ = stack[4].m_obj;
lean_object* v_a_4008_ = stack[5].m_obj;
lean_object* v_a_4009_ = stack[6].m_obj;
lean_object* v_a_4010_ = stack[7].m_obj;
lean_object* v_a_4011_ = stack[8].m_obj;
lean_object* v_a_4012_ = stack[9].m_obj;
lean_object* v_a_4013_ = stack[10].m_obj;
lean_object* v_res_4133_;
v_res_4133_ = l_Lean_Meta_Grind_propagateBoolAndUp(v_e_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_);
stack->m_obj
 = v_res_4133_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp___boxed(lean_object* v_e_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_Grind_propagateBoolAndUp(v_e_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec(v_a_4135_);
return v_res_4146_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4149_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp___boxed), 12, 0);
v___x_4150_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4148_, v___x_4149_);
return v___x_4150_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4151_;
v_res_4151_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4151_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9____boxed(lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndUp___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_3683843215____hygCtx___hyg_9_();
return v_res_4153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1(void){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = lean_box(0);
v___x_4160_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__0));
v___x_4161_ = l_Lean_mkConst(v___x_4160_, v___x_4159_);
return v___x_4161_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4167_ = lean_box(0);
v___x_4168_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndDown___closed__2));
v___x_4169_ = l_Lean_mkConst(v___x_4168_, v___x_4167_);
return v___x_4169_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* v_e_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v___x_4185_; 
lean_inc_ref(v_e_4170_);
v___x_4185_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4170_, v_a_4171_, v_a_4175_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4220_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4220_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4220_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
uint8_t v___x_4190_; 
v___x_4190_ = lean_unbox(v_a_4186_);
lean_dec(v_a_4186_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4193_; 
lean_dec_ref(v_e_4170_);
v___x_4191_ = lean_box(0);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4191_);
v___x_4193_ = v___x_4188_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
else
{
lean_object* v___x_4195_; uint8_t v___x_4196_; 
lean_del_object(v___x_4188_);
lean_inc_ref(v_e_4170_);
v___x_4195_ = l_Lean_Expr_cleanupAnnotations(v_e_4170_);
v___x_4196_ = l_Lean_Expr_isApp(v___x_4195_);
if (v___x_4196_ == 0)
{
lean_dec_ref(v___x_4195_);
lean_dec_ref(v_e_4170_);
goto v___jp_4182_;
}
else
{
lean_object* v_arg_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v_arg_4197_ = lean_ctor_get(v___x_4195_, 1);
lean_inc_ref(v_arg_4197_);
v___x_4198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4195_);
v___x_4199_ = l_Lean_Expr_isApp(v___x_4198_);
if (v___x_4199_ == 0)
{
lean_dec_ref(v___x_4198_);
lean_dec_ref(v_arg_4197_);
lean_dec_ref(v_e_4170_);
goto v___jp_4182_;
}
else
{
lean_object* v_arg_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v_arg_4200_ = lean_ctor_get(v___x_4198_, 1);
lean_inc_ref(v_arg_4200_);
v___x_4201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4198_);
v___x_4202_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4203_ = l_Lean_Expr_isConstOf(v___x_4201_, v___x_4202_);
lean_dec_ref(v___x_4201_);
if (v___x_4203_ == 0)
{
lean_dec_ref(v_arg_4200_);
lean_dec_ref(v_arg_4197_);
lean_dec_ref(v_e_4170_);
goto v___jp_4182_;
}
else
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc_n(v_a_4205_, 2);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__1, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__1);
lean_inc_ref(v_arg_4197_);
lean_inc_ref_n(v_arg_4200_, 2);
v___x_4207_ = l_Lean_mkApp3(v___x_4206_, v_arg_4200_, v_arg_4197_, v_a_4205_);
v___x_4208_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4200_, v___x_4207_, v_a_4171_, v_a_4173_, v_a_4175_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec_ref_known(v___x_4208_, 1);
v___x_4209_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolAndDown___closed__3, &l_Lean_Meta_Grind_propagateBoolAndDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolAndDown___closed__3);
lean_inc_ref(v_arg_4197_);
v___x_4210_ = l_Lean_mkApp3(v___x_4209_, v_arg_4200_, v_arg_4197_, v_a_4205_);
v___x_4211_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4197_, v___x_4210_, v_a_4171_, v_a_4173_, v_a_4175_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
return v___x_4211_;
}
else
{
lean_dec(v_a_4205_);
lean_dec_ref(v_arg_4200_);
lean_dec_ref(v_arg_4197_);
return v___x_4208_;
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v_arg_4200_);
lean_dec_ref(v_arg_4197_);
v_a_4212_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4204_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4204_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
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
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v_e_4170_);
v_a_4221_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4185_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4185_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
v___jp_4182_:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = lean_box(0);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
return v___x_4184_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolAndDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4170_ = stack[0].m_obj;
lean_object* v_a_4171_ = stack[1].m_obj;
lean_object* v_a_4172_ = stack[2].m_obj;
lean_object* v_a_4173_ = stack[3].m_obj;
lean_object* v_a_4174_ = stack[4].m_obj;
lean_object* v_a_4175_ = stack[5].m_obj;
lean_object* v_a_4176_ = stack[6].m_obj;
lean_object* v_a_4177_ = stack[7].m_obj;
lean_object* v_a_4178_ = stack[8].m_obj;
lean_object* v_a_4179_ = stack[9].m_obj;
lean_object* v_a_4180_ = stack[10].m_obj;
lean_object* v_res_4229_;
v_res_4229_ = l_Lean_Meta_Grind_propagateBoolAndDown(v_e_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
stack->m_obj
 = v_res_4229_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown___boxed(lean_object* v_e_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Meta_Grind_propagateBoolAndDown(v_e_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
lean_dec(v_a_4232_);
lean_dec(v_a_4231_);
return v_res_4242_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolAndUp___closed__1));
v___x_4245_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown___boxed), 12, 0);
v___x_4246_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4244_, v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4247_;
v_res_4247_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4247_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9____boxed(lean_object* v_a_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolAndDown___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_2508836509____hygCtx___hyg_9_();
return v_res_4249_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3(void){
_start:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = lean_box(0);
v___x_4260_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__2));
v___x_4261_ = l_Lean_mkConst(v___x_4260_, v___x_4259_);
return v___x_4261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5(void){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = lean_box(0);
v___x_4268_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__4));
v___x_4269_ = l_Lean_mkConst(v___x_4268_, v___x_4267_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_box(0);
v___x_4276_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__6));
v___x_4277_ = l_Lean_mkConst(v___x_4276_, v___x_4275_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4283_ = lean_box(0);
v___x_4284_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__8));
v___x_4285_ = l_Lean_mkConst(v___x_4284_, v___x_4283_);
return v___x_4285_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* v_e_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
lean_inc_ref(v_e_4286_);
v___x_4301_ = l_Lean_Expr_cleanupAnnotations(v_e_4286_);
v___x_4302_ = l_Lean_Expr_isApp(v___x_4301_);
if (v___x_4302_ == 0)
{
lean_dec_ref(v___x_4301_);
lean_dec_ref(v_e_4286_);
goto v___jp_4298_;
}
else
{
lean_object* v_arg_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v_arg_4303_ = lean_ctor_get(v___x_4301_, 1);
lean_inc_ref(v_arg_4303_);
v___x_4304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4301_);
v___x_4305_ = l_Lean_Expr_isApp(v___x_4304_);
if (v___x_4305_ == 0)
{
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
goto v___jp_4298_;
}
else
{
lean_object* v_arg_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_arg_4306_ = lean_ctor_get(v___x_4304_, 1);
lean_inc_ref(v_arg_4306_);
v___x_4307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4304_);
v___x_4308_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4309_ = l_Lean_Expr_isConstOf(v___x_4307_, v___x_4308_);
lean_dec_ref(v___x_4307_);
if (v___x_4309_ == 0)
{
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
goto v___jp_4298_;
}
else
{
lean_object* v___x_4310_; 
lean_inc_ref(v_arg_4306_);
v___x_4310_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4306_, v_a_4287_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; uint8_t v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v___x_4312_ = lean_unbox(v_a_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_inc_ref(v_arg_4303_);
v___x_4313_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4303_, v_a_4287_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; uint8_t v___x_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = lean_unbox(v_a_4314_);
lean_dec(v_a_4314_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; 
lean_dec(v_a_4311_);
lean_inc_ref(v_arg_4306_);
v___x_4316_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4306_, v_a_4287_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; uint8_t v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = lean_unbox(v_a_4317_);
lean_dec(v_a_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; 
lean_inc_ref(v_arg_4303_);
v___x_4319_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4303_, v_a_4287_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4342_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4342_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4342_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
uint8_t v___x_4324_; 
v___x_4324_ = lean_unbox(v_a_4320_);
lean_dec(v_a_4320_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4325_; lean_object* v___x_4327_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v___x_4325_ = lean_box(0);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v___x_4325_);
v___x_4327_ = v___x_4322_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4325_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
else
{
lean_object* v___x_4329_; 
lean_del_object(v___x_4322_);
lean_inc_ref(v_arg_4303_);
v___x_4329_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4303_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4329_, 1);
v___x_4331_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__3, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__3);
v___x_4332_ = l_Lean_mkApp3(v___x_4331_, v_arg_4306_, v_arg_4303_, v_a_4330_);
v___x_4333_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4286_, v___x_4332_, v_a_4287_, v_a_4289_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4333_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4334_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4329_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4329_);
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
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4343_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4319_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4319_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v___x_4351_; 
lean_inc_ref(v_arg_4306_);
v___x_4351_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4306_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__5, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__5);
v___x_4354_ = l_Lean_mkApp3(v___x_4353_, v_arg_4306_, v_arg_4303_, v_a_4352_);
v___x_4355_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4286_, v___x_4354_, v_a_4287_, v_a_4289_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4355_;
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4356_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4351_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4351_);
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
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4364_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4316_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4316_);
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
else
{
lean_object* v___x_4372_; 
lean_inc_ref(v_arg_4303_);
v___x_4372_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4303_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; uint8_t v___x_4376_; lean_object* v___x_4377_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v___x_4374_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__7, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__7);
lean_inc_ref(v_arg_4306_);
v___x_4375_ = l_Lean_mkApp3(v___x_4374_, v_arg_4306_, v_arg_4303_, v_a_4373_);
v___x_4376_ = lean_unbox(v_a_4311_);
lean_dec(v_a_4311_);
v___x_4377_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4286_, v_arg_4306_, v___x_4375_, v___x_4376_, v_a_4287_, v_a_4289_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4377_;
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec(v_a_4311_);
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4378_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4372_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4372_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v_a_4311_);
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4386_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4313_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4313_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_object* v___x_4394_; 
lean_dec(v_a_4311_);
lean_inc_ref(v_arg_4306_);
v___x_4394_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4306_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; uint8_t v___x_4398_; lean_object* v___x_4399_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrUp___closed__9, &l_Lean_Meta_Grind_propagateBoolOrUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateBoolOrUp___closed__9);
lean_inc_ref(v_arg_4303_);
v___x_4397_ = l_Lean_mkApp3(v___x_4396_, v_arg_4306_, v_arg_4303_, v_a_4395_);
v___x_4398_ = 0;
v___x_4399_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_4286_, v_arg_4303_, v___x_4397_, v___x_4398_, v_a_4287_, v_a_4289_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4400_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4394_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4394_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec_ref(v_arg_4306_);
lean_dec_ref(v_arg_4303_);
lean_dec_ref(v_e_4286_);
v_a_4408_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4310_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4310_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
}
v___jp_4298_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_box(0);
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4299_);
return v___x_4300_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolOrUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4286_ = stack[0].m_obj;
lean_object* v_a_4287_ = stack[1].m_obj;
lean_object* v_a_4288_ = stack[2].m_obj;
lean_object* v_a_4289_ = stack[3].m_obj;
lean_object* v_a_4290_ = stack[4].m_obj;
lean_object* v_a_4291_ = stack[5].m_obj;
lean_object* v_a_4292_ = stack[6].m_obj;
lean_object* v_a_4293_ = stack[7].m_obj;
lean_object* v_a_4294_ = stack[8].m_obj;
lean_object* v_a_4295_ = stack[9].m_obj;
lean_object* v_a_4296_ = stack[10].m_obj;
lean_object* v_res_4416_;
v_res_4416_ = l_Lean_Meta_Grind_propagateBoolOrUp(v_e_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_);
stack->m_obj
 = v_res_4416_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp___boxed(lean_object* v_e_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_Meta_Grind_propagateBoolOrUp(v_e_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_);
lean_dec(v_a_4427_);
lean_dec_ref(v_a_4426_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
lean_dec(v_a_4419_);
lean_dec(v_a_4418_);
return v_res_4429_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4432_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp___boxed), 12, 0);
v___x_4433_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4431_, v___x_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4434_;
v_res_4434_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9____boxed(lean_object* v_a_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrUp___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_428936191____hygCtx___hyg_9_();
return v_res_4436_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1(void){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = lean_box(0);
v___x_4443_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__0));
v___x_4444_ = l_Lean_mkConst(v___x_4443_, v___x_4442_);
return v___x_4444_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_box(0);
v___x_4451_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrDown___closed__2));
v___x_4452_ = l_Lean_mkConst(v___x_4451_, v___x_4450_);
return v___x_4452_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* v_e_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v___x_4468_; 
lean_inc_ref(v_e_4453_);
v___x_4468_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4453_, v_a_4454_, v_a_4458_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4503_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4471_ = v___x_4468_;
v_isShared_4472_ = v_isSharedCheck_4503_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4503_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
uint8_t v___x_4473_; 
v___x_4473_ = lean_unbox(v_a_4469_);
lean_dec(v_a_4469_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; lean_object* v___x_4476_; 
lean_dec_ref(v_e_4453_);
v___x_4474_ = lean_box(0);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 0, v___x_4474_);
v___x_4476_ = v___x_4471_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
else
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
lean_del_object(v___x_4471_);
lean_inc_ref(v_e_4453_);
v___x_4478_ = l_Lean_Expr_cleanupAnnotations(v_e_4453_);
v___x_4479_ = l_Lean_Expr_isApp(v___x_4478_);
if (v___x_4479_ == 0)
{
lean_dec_ref(v___x_4478_);
lean_dec_ref(v_e_4453_);
goto v___jp_4465_;
}
else
{
lean_object* v_arg_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v_arg_4480_ = lean_ctor_get(v___x_4478_, 1);
lean_inc_ref(v_arg_4480_);
v___x_4481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4478_);
v___x_4482_ = l_Lean_Expr_isApp(v___x_4481_);
if (v___x_4482_ == 0)
{
lean_dec_ref(v___x_4481_);
lean_dec_ref(v_arg_4480_);
lean_dec_ref(v_e_4453_);
goto v___jp_4465_;
}
else
{
lean_object* v_arg_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v_arg_4483_ = lean_ctor_get(v___x_4481_, 1);
lean_inc_ref(v_arg_4483_);
v___x_4484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4481_);
v___x_4485_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4486_ = l_Lean_Expr_isConstOf(v___x_4484_, v___x_4485_);
lean_dec_ref(v___x_4484_);
if (v___x_4486_ == 0)
{
lean_dec_ref(v_arg_4483_);
lean_dec_ref(v_arg_4480_);
lean_dec_ref(v_e_4453_);
goto v___jp_4465_;
}
else
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc_n(v_a_4488_, 2);
lean_dec_ref_known(v___x_4487_, 1);
v___x_4489_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__1, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__1);
lean_inc_ref(v_arg_4480_);
lean_inc_ref_n(v_arg_4483_, 2);
v___x_4490_ = l_Lean_mkApp3(v___x_4489_, v_arg_4483_, v_arg_4480_, v_a_4488_);
v___x_4491_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4483_, v___x_4490_, v_a_4454_, v_a_4456_, v_a_4458_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
lean_dec_ref_known(v___x_4491_, 1);
v___x_4492_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolOrDown___closed__3, &l_Lean_Meta_Grind_propagateBoolOrDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolOrDown___closed__3);
lean_inc_ref(v_arg_4480_);
v___x_4493_ = l_Lean_mkApp3(v___x_4492_, v_arg_4483_, v_arg_4480_, v_a_4488_);
v___x_4494_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4480_, v___x_4493_, v_a_4454_, v_a_4456_, v_a_4458_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
return v___x_4494_;
}
else
{
lean_dec(v_a_4488_);
lean_dec_ref(v_arg_4483_);
lean_dec_ref(v_arg_4480_);
return v___x_4491_;
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec_ref(v_arg_4483_);
lean_dec_ref(v_arg_4480_);
v_a_4495_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4487_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4487_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
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
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v_e_4453_);
v_a_4504_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4468_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4468_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
v___jp_4465_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4466_ = lean_box(0);
v___x_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
return v___x_4467_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolOrDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4453_ = stack[0].m_obj;
lean_object* v_a_4454_ = stack[1].m_obj;
lean_object* v_a_4455_ = stack[2].m_obj;
lean_object* v_a_4456_ = stack[3].m_obj;
lean_object* v_a_4457_ = stack[4].m_obj;
lean_object* v_a_4458_ = stack[5].m_obj;
lean_object* v_a_4459_ = stack[6].m_obj;
lean_object* v_a_4460_ = stack[7].m_obj;
lean_object* v_a_4461_ = stack[8].m_obj;
lean_object* v_a_4462_ = stack[9].m_obj;
lean_object* v_a_4463_ = stack[10].m_obj;
lean_object* v_res_4512_;
v_res_4512_ = l_Lean_Meta_Grind_propagateBoolOrDown(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
stack->m_obj
 = v_res_4512_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown___boxed(lean_object* v_e_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_Meta_Grind_propagateBoolOrDown(v_e_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec(v_a_4514_);
return v_res_4525_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolOrUp___closed__1));
v___x_4528_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown___boxed), 12, 0);
v___x_4529_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4527_, v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4530_;
v_res_4530_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4530_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9____boxed(lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolOrDown___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_201731281____hygCtx___hyg_9_();
return v_res_4532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3(void){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4542_ = lean_box(0);
v___x_4543_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__2));
v___x_4544_ = l_Lean_mkConst(v___x_4543_, v___x_4542_);
return v___x_4544_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = lean_box(0);
v___x_4551_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__4));
v___x_4552_ = l_Lean_mkConst(v___x_4551_, v___x_4550_);
return v___x_4552_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = lean_box(0);
v___x_4559_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__6));
v___x_4560_ = l_Lean_mkConst(v___x_4559_, v___x_4558_);
return v___x_4560_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* v_e_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
lean_inc_ref(v_e_4561_);
v___x_4576_ = l_Lean_Expr_cleanupAnnotations(v_e_4561_);
v___x_4577_ = l_Lean_Expr_isApp(v___x_4576_);
if (v___x_4577_ == 0)
{
lean_dec_ref(v___x_4576_);
lean_dec_ref(v_e_4561_);
goto v___jp_4573_;
}
else
{
lean_object* v_arg_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; 
v_arg_4578_ = lean_ctor_get(v___x_4576_, 1);
lean_inc_ref(v_arg_4578_);
v___x_4579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4576_);
v___x_4580_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4581_ = l_Lean_Expr_isConstOf(v___x_4579_, v___x_4580_);
lean_dec_ref(v___x_4579_);
if (v___x_4581_ == 0)
{
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
goto v___jp_4573_;
}
else
{
lean_object* v___x_4582_; 
lean_inc_ref(v_arg_4578_);
v___x_4582_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_arg_4578_, v_a_4562_, v_a_4566_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; uint8_t v___x_4584_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4582_, 1);
v___x_4584_ = lean_unbox(v_a_4583_);
lean_dec(v_a_4583_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; 
lean_inc_ref(v_arg_4578_);
v___x_4585_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_arg_4578_, v_a_4562_, v_a_4566_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; uint8_t v___x_4587_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4585_, 1);
v___x_4587_ = lean_unbox(v_a_4586_);
lean_dec(v_a_4586_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; 
v___x_4588_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4561_, v_arg_4578_, v_a_4562_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4611_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4591_ = v___x_4588_;
v_isShared_4592_ = v_isSharedCheck_4611_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4588_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4611_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
uint8_t v___x_4593_; 
v___x_4593_ = lean_unbox(v_a_4589_);
lean_dec(v_a_4589_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; lean_object* v___x_4596_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v___x_4594_ = lean_box(0);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 0, v___x_4594_);
v___x_4596_ = v___x_4591_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
else
{
lean_object* v___x_4598_; 
lean_del_object(v___x_4591_);
lean_inc(v_a_4571_);
lean_inc_ref(v_a_4570_);
lean_inc(v_a_4569_);
lean_inc_ref(v_a_4568_);
lean_inc(v_a_4567_);
lean_inc_ref(v_a_4566_);
lean_inc(v_a_4565_);
lean_inc_ref(v_a_4564_);
lean_inc(v_a_4563_);
lean_inc(v_a_4562_);
lean_inc_ref(v_arg_4578_);
v___x_4598_ = lean_grind_mk_eq_proof(v_e_4561_, v_arg_4578_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v___x_4600_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4601_ = l_Lean_mkAppB(v___x_4600_, v_arg_4578_, v_a_4599_);
v___x_4602_ = l_Lean_Meta_Grind_closeGoal(v___x_4601_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4602_;
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec_ref(v_arg_4578_);
v_a_4603_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4598_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4598_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
}
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v_a_4612_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4588_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4588_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
else
{
lean_object* v___x_4620_; 
lean_inc_ref(v_arg_4578_);
v___x_4620_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_arg_4578_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref_known(v___x_4620_, 1);
v___x_4622_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__5, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__5);
v___x_4623_ = l_Lean_mkAppB(v___x_4622_, v_arg_4578_, v_a_4621_);
v___x_4624_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_e_4561_, v___x_4623_, v_a_4562_, v_a_4564_, v_a_4566_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4624_;
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v_a_4625_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4620_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4620_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v_a_4633_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4585_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4585_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
else
{
lean_object* v___x_4641_; 
lean_inc_ref(v_arg_4578_);
v___x_4641_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_arg_4578_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref_known(v___x_4641_, 1);
v___x_4643_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__7, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__7);
v___x_4644_ = l_Lean_mkAppB(v___x_4643_, v_arg_4578_, v_a_4642_);
v___x_4645_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_e_4561_, v___x_4644_, v_a_4562_, v_a_4564_, v_a_4566_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4645_;
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v_a_4646_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4641_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4641_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v_arg_4578_);
lean_dec_ref(v_e_4561_);
v_a_4654_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4582_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4582_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
v___jp_4573_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = lean_box(0);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolNotUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4561_ = stack[0].m_obj;
lean_object* v_a_4562_ = stack[1].m_obj;
lean_object* v_a_4563_ = stack[2].m_obj;
lean_object* v_a_4564_ = stack[3].m_obj;
lean_object* v_a_4565_ = stack[4].m_obj;
lean_object* v_a_4566_ = stack[5].m_obj;
lean_object* v_a_4567_ = stack[6].m_obj;
lean_object* v_a_4568_ = stack[7].m_obj;
lean_object* v_a_4569_ = stack[8].m_obj;
lean_object* v_a_4570_ = stack[9].m_obj;
lean_object* v_a_4571_ = stack[10].m_obj;
lean_object* v_res_4662_;
v_res_4662_ = l_Lean_Meta_Grind_propagateBoolNotUp(v_e_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
stack->m_obj
 = v_res_4662_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp___boxed(lean_object* v_e_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_Meta_Grind_propagateBoolNotUp(v_e_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
lean_dec(v_a_4669_);
lean_dec_ref(v_a_4668_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec(v_a_4664_);
return v_res_4675_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4678_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp___boxed), 12, 0);
v___x_4679_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4677_, v___x_4678_);
return v___x_4679_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4680_;
v_res_4680_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4680_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9____boxed(lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotUp___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_1440696379____hygCtx___hyg_9_();
return v_res_4682_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4688_ = lean_box(0);
v___x_4689_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__0));
v___x_4690_ = l_Lean_mkConst(v___x_4689_, v___x_4688_);
return v___x_4690_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4696_ = lean_box(0);
v___x_4697_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotDown___closed__2));
v___x_4698_ = l_Lean_mkConst(v___x_4697_, v___x_4696_);
return v___x_4698_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* v_e_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
lean_inc_ref(v_e_4699_);
v___x_4714_ = l_Lean_Expr_cleanupAnnotations(v_e_4699_);
v___x_4715_ = l_Lean_Expr_isApp(v___x_4714_);
if (v___x_4715_ == 0)
{
lean_dec_ref(v___x_4714_);
lean_dec_ref(v_e_4699_);
goto v___jp_4711_;
}
else
{
lean_object* v_arg_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; 
v_arg_4716_ = lean_ctor_get(v___x_4714_, 1);
lean_inc_ref(v_arg_4716_);
v___x_4717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4714_);
v___x_4718_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4719_ = l_Lean_Expr_isConstOf(v___x_4717_, v___x_4718_);
lean_dec_ref(v___x_4717_);
if (v___x_4719_ == 0)
{
lean_dec_ref(v_arg_4716_);
lean_dec_ref(v_e_4699_);
goto v___jp_4711_;
}
else
{
lean_object* v___x_4720_; 
lean_inc_ref(v_e_4699_);
v___x_4720_ = l_Lean_Meta_Grind_isEqBoolFalse___redArg(v_e_4699_, v_a_4700_, v_a_4704_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; uint8_t v___x_4722_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v___x_4722_ = lean_unbox(v_a_4721_);
lean_dec(v_a_4721_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; 
lean_inc_ref(v_e_4699_);
v___x_4723_ = l_Lean_Meta_Grind_isEqBoolTrue___redArg(v_e_4699_, v_a_4700_, v_a_4704_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; uint8_t v___x_4725_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = lean_unbox(v_a_4724_);
lean_dec(v_a_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Meta_Grind_isEqv___redArg(v_e_4699_, v_arg_4716_, v_a_4700_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4749_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4729_ = v___x_4726_;
v_isShared_4730_ = v_isSharedCheck_4749_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4726_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4749_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
uint8_t v___x_4731_; 
v___x_4731_ = lean_unbox(v_a_4727_);
lean_dec(v_a_4727_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; lean_object* v___x_4734_; 
lean_dec_ref(v_arg_4716_);
lean_dec_ref(v_e_4699_);
v___x_4732_ = lean_box(0);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 0, v___x_4732_);
v___x_4734_ = v___x_4729_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4732_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
else
{
lean_object* v___x_4736_; 
lean_del_object(v___x_4729_);
lean_inc(v_a_4709_);
lean_inc_ref(v_a_4708_);
lean_inc(v_a_4707_);
lean_inc_ref(v_a_4706_);
lean_inc(v_a_4705_);
lean_inc_ref(v_a_4704_);
lean_inc(v_a_4703_);
lean_inc_ref(v_a_4702_);
lean_inc(v_a_4701_);
lean_inc(v_a_4700_);
lean_inc_ref(v_arg_4716_);
v___x_4736_ = lean_grind_mk_eq_proof(v_e_4699_, v_arg_4716_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotUp___closed__3, &l_Lean_Meta_Grind_propagateBoolNotUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotUp___closed__3);
v___x_4739_ = l_Lean_mkAppB(v___x_4738_, v_arg_4716_, v_a_4737_);
v___x_4740_ = l_Lean_Meta_Grind_closeGoal(v___x_4739_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
return v___x_4740_;
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec_ref(v_arg_4716_);
v_a_4741_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4736_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4736_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec_ref(v_arg_4716_);
lean_dec_ref(v_e_4699_);
v_a_4750_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4726_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4726_);
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
else
{
lean_object* v___x_4758_; 
v___x_4758_ = l_Lean_Meta_Grind_mkEqBoolTrueProof(v_e_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4758_, 1);
v___x_4760_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__1, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__1_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__1);
lean_inc_ref(v_arg_4716_);
v___x_4761_ = l_Lean_mkAppB(v___x_4760_, v_arg_4716_, v_a_4759_);
v___x_4762_ = l_Lean_Meta_Grind_pushEqBoolFalse___redArg(v_arg_4716_, v___x_4761_, v_a_4700_, v_a_4702_, v_a_4704_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
return v___x_4762_;
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v_arg_4716_);
v_a_4763_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4758_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4758_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v_arg_4716_);
lean_dec_ref(v_e_4699_);
v_a_4771_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4723_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4723_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v___x_4779_; 
v___x_4779_ = l_Lean_Meta_Grind_mkEqBoolFalseProof(v_e_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref_known(v___x_4779_, 1);
v___x_4781_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBoolNotDown___closed__3, &l_Lean_Meta_Grind_propagateBoolNotDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateBoolNotDown___closed__3);
lean_inc_ref(v_arg_4716_);
v___x_4782_ = l_Lean_mkAppB(v___x_4781_, v_arg_4716_, v_a_4780_);
v___x_4783_ = l_Lean_Meta_Grind_pushEqBoolTrue___redArg(v_arg_4716_, v___x_4782_, v_a_4700_, v_a_4702_, v_a_4704_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
return v___x_4783_;
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec_ref(v_arg_4716_);
v_a_4784_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4779_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4779_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v_arg_4716_);
lean_dec_ref(v_e_4699_);
v_a_4792_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4720_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4720_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
v___jp_4711_:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = lean_box(0);
v___x_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
return v___x_4713_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBoolNotDown_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4699_ = stack[0].m_obj;
lean_object* v_a_4700_ = stack[1].m_obj;
lean_object* v_a_4701_ = stack[2].m_obj;
lean_object* v_a_4702_ = stack[3].m_obj;
lean_object* v_a_4703_ = stack[4].m_obj;
lean_object* v_a_4704_ = stack[5].m_obj;
lean_object* v_a_4705_ = stack[6].m_obj;
lean_object* v_a_4706_ = stack[7].m_obj;
lean_object* v_a_4707_ = stack[8].m_obj;
lean_object* v_a_4708_ = stack[9].m_obj;
lean_object* v_a_4709_ = stack[10].m_obj;
lean_object* v_res_4800_;
v_res_4800_ = l_Lean_Meta_Grind_propagateBoolNotDown(v_e_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_);
stack->m_obj
 = v_res_4800_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown___boxed(lean_object* v_e_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Lean_Meta_Grind_propagateBoolNotDown(v_e_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec(v_a_4802_);
return v_res_4813_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBoolNotUp___closed__1));
v___x_4816_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown___boxed), 12, 0);
v___x_4817_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4815_, v___x_4816_);
return v___x_4817_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4818_;
v_res_4818_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9____boxed(lean_object* v_a_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l___private_Lean_Meta_Tactic_Grind_Propagate_0__Lean_Meta_Grind_propagateBoolNotDown___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_Propagate_434325315____hygCtx___hyg_9_();
return v_res_4820_;
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
