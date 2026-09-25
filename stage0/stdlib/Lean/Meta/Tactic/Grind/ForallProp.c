// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: public import Init.Grind.Propagator import Init.Simproc import Init.Grind.Norm import Lean.Meta.Tactic.Grind.Internalize import Lean.Meta.Tactic.Grind.Anchor import Lean.Meta.Tactic.Grind.EqResolution import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Grind.Lemmas
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_false_of_imp_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 135, 203, 106, 42, 89, 33, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "imp_eq_of_eq_true_right"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 104, 37, 206, 110, 37, 230, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "imp_eq_of_eq_true_left"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(71, 219, 112, 102, 237, 48, 138, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "imp_eq_of_eq_false_left"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value),LEAN_SCALAR_PTR_LITERAL(71, 59, 221, 124, 3, 234, 184, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "forall_propagator"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 98, 167, 92, 43, 63, 200, 147)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forallPropagator"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(62, 20, 227, 217, 136, 128, 93, 131)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "q': "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " for"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropUp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isEqTrue, "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 104, 189, 185, 38, 81, 44, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(50, 213, 255, 45, 151, 209, 83, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to create E-match local theorem for"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "eqResolution"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 23, 253, 34, 8, 106, 124, 207)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_forall_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value),LEAN_SCALAR_PTR_LITERAL(173, 140, 239, 244, 206, 215, 220, 192)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_true_of_imp_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 202, 44, 200, 3, 215, 155, 153)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
static const lean_string_object l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "eq_false_of_imp_eq_false"};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value),LEAN_SCALAR_PTR_LITERAL(224, 133, 152, 168, 210, 40, 234, 100)}};
static const lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateExistsDown___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_propagateExistsDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_propagateExistsDown___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "forall_not_of_not_exists"};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateExistsDown___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__6_value),LEAN_SCALAR_PTR_LITERAL(64, 176, 52, 188, 216, 118, 163, 15)}};
static const lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateExistsDown___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "forall_and"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value),LEAN_SCALAR_PTR_LITERAL(81, 10, 210, 75, 235, 208, 8, 129)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_forall_or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 112, 166, 94, 237, 48, 167, 129)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_or_forall"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 14, 212, 131, 198, 226, 199, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__13;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_self_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value),LEAN_SCALAR_PTR_LITERAL(166, 96, 8, 70, 216, 37, 74, 175)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__16;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_imp_eq_or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value),LEAN_SCALAR_PTR_LITERAL(61, 240, 249, 78, 172, 240, 254, 86)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_true_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value),LEAN_SCALAR_PTR_LITERAL(23, 129, 235, 110, 107, 55, 234, 42)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__21;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__27;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__33;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__34_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__35_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__36;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__37;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__38;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__39_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__41;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpForall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 161, 230, 164, 57, 132, 181, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "exists_const"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 209, 190, 134, 241, 243, 173, 71)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_prop"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 14, 159, 153, 168, 50, 182, 0)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpExists___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpExists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value),LEAN_SCALAR_PTR_LITERAL(220, 43, 168, 20, 165, 143, 80, 231)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3));
v___x_10_ = l_Lean_mkConst(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___x_17_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6));
v___x_18_ = l_Lean_mkConst(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_box(0);
v___x_25_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9));
v___x_26_ = l_Lean_mkConst(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12));
v___x_34_ = l_Lean_mkConst(v___x_33_, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_b_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___y_50_; lean_object* v___y_93_; uint8_t v___y_125_; lean_object* v___y_126_; lean_object* v___y_155_; lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_b_37_, v_a_38_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_200_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_200_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_200_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
uint8_t v___x_191_; 
v___x_191_ = lean_unbox(v_a_187_);
lean_dec(v_a_187_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v___x_192_ = lean_box(0);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_196_; 
lean_del_object(v___x_189_);
lean_inc_ref(v_a_36_);
v___x_196_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_36_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
v___x_198_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_198_ == 0)
{
v___y_155_ = v___x_196_;
goto v___jp_154_;
}
else
{
lean_object* v___x_199_; 
lean_dec_ref_known(v___x_196_, 1);
lean_inc_ref(v_b_37_);
v___x_199_ = l_Lean_Meta_isProp(v_b_37_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
v___y_155_ = v___x_199_;
goto v___jp_154_;
}
}
else
{
v___y_155_ = v___x_196_;
goto v___jp_154_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_201_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_186_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
v___jp_49_:
{
if (lean_obj_tag(v___y_50_) == 0)
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_83_; 
v_a_51_ = lean_ctor_get(v___y_50_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___y_50_);
if (v_isSharedCheck_83_ == 0)
{
v___x_53_ = v___y_50_;
v_isShared_54_ = v_isSharedCheck_83_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___y_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_83_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint8_t v___x_55_; 
v___x_55_ = lean_unbox(v_a_51_);
lean_dec(v_a_51_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v___x_56_ = lean_box(0);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_56_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v___x_60_; 
lean_del_object(v___x_53_);
v___x_60_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_35_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
lean_inc_ref(v_b_37_);
v___x_62_ = l_Lean_Meta_Grind_mkEqFalseProof(v_b_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_62_, 1);
v___x_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_a_36_);
v___x_65_ = l_Lean_mkApp4(v___x_64_, v_a_36_, v_b_37_, v_a_61_, v_a_63_);
v___x_66_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_36_, v___x_65_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_61_);
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
v_a_67_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_62_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_62_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
v_a_75_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_60_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_60_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_84_ = lean_ctor_get(v___y_50_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___y_50_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___y_50_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___y_50_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
v___jp_92_:
{
if (lean_obj_tag(v___y_93_) == 0)
{
lean_object* v_a_94_; uint8_t v___x_95_; 
v_a_94_ = lean_ctor_get(v___y_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___y_93_, 1);
v___x_95_ = lean_unbox(v_a_94_);
lean_dec(v_a_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_inc_ref(v_b_37_);
v___x_96_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_37_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; uint8_t v___x_98_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v___x_98_ = lean_unbox(v_a_97_);
lean_dec(v_a_97_);
if (v___x_98_ == 0)
{
v___y_50_ = v___x_96_;
goto v___jp_49_;
}
else
{
lean_object* v___x_99_; 
lean_dec_ref_known(v___x_96_, 1);
lean_inc_ref(v_e_35_);
v___x_99_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_35_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; uint8_t v___x_101_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v___x_101_ = lean_unbox(v_a_100_);
lean_dec(v_a_100_);
if (v___x_101_ == 0)
{
v___y_50_ = v___x_99_;
goto v___jp_49_;
}
else
{
lean_object* v___x_102_; 
lean_dec_ref_known(v___x_99_, 1);
lean_inc_ref(v_a_36_);
v___x_102_ = l_Lean_Meta_isProp(v_a_36_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
v___y_50_ = v___x_102_;
goto v___jp_49_;
}
}
else
{
v___y_50_ = v___x_99_;
goto v___jp_49_;
}
}
}
else
{
v___y_50_ = v___x_96_;
goto v___jp_49_;
}
}
else
{
lean_object* v___x_103_; 
lean_inc_ref(v_b_37_);
v___x_103_ = l_Lean_Meta_Grind_mkEqTrueProof(v_b_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
v___x_106_ = l_Lean_mkApp3(v___x_105_, v_a_36_, v_b_37_, v_a_104_);
v___x_107_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_35_, v___x_106_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_107_;
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
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
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_116_ = lean_ctor_get(v___y_93_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___y_93_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___y_93_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___y_93_);
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
v___jp_124_:
{
if (lean_obj_tag(v___y_126_) == 0)
{
lean_object* v_a_127_; uint8_t v___x_128_; 
v_a_127_ = lean_ctor_get(v___y_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___y_126_, 1);
v___x_128_ = lean_unbox(v_a_127_);
lean_dec(v_a_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_inc_ref(v_b_37_);
v___x_129_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_37_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; uint8_t v___x_131_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
v___x_131_ = lean_unbox(v_a_130_);
lean_dec(v_a_130_);
if (v___x_131_ == 0)
{
v___y_93_ = v___x_129_;
goto v___jp_92_;
}
else
{
lean_object* v___x_132_; 
lean_dec_ref_known(v___x_129_, 1);
lean_inc_ref(v_a_36_);
v___x_132_ = l_Lean_Meta_isProp(v_a_36_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
v___y_93_ = v___x_132_;
goto v___jp_92_;
}
}
else
{
v___y_93_ = v___x_129_;
goto v___jp_92_;
}
}
else
{
lean_object* v___x_133_; 
lean_inc_ref(v_a_36_);
v___x_133_ = l_Lean_Meta_Grind_mkEqTrueProof(v_a_36_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
lean_inc_ref(v_b_37_);
v___x_136_ = l_Lean_mkApp3(v___x_135_, v_a_36_, v_b_37_, v_a_134_);
v___x_137_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_35_, v_b_37_, v___x_136_, v___y_125_, v_a_38_, v_a_40_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_137_;
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_138_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_133_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_133_);
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
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_146_ = lean_ctor_get(v___y_126_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___y_126_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___y_126_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___y_126_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
v___jp_154_:
{
if (lean_obj_tag(v___y_155_) == 0)
{
lean_object* v_a_156_; uint8_t v___x_157_; 
v_a_156_ = lean_ctor_get(v___y_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___y_155_, 1);
v___x_157_ = lean_unbox(v_a_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_inc_ref(v_a_36_);
v___x_158_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_36_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
v___x_160_ = lean_unbox(v_a_159_);
lean_dec(v_a_159_);
if (v___x_160_ == 0)
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_a_156_);
lean_dec(v_a_156_);
v___y_125_ = v___x_161_;
v___y_126_ = v___x_158_;
goto v___jp_124_;
}
else
{
lean_object* v___x_162_; uint8_t v___x_163_; 
lean_dec_ref_known(v___x_158_, 1);
lean_inc_ref(v_b_37_);
v___x_162_ = l_Lean_Meta_isProp(v_b_37_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
v___x_163_ = lean_unbox(v_a_156_);
lean_dec(v_a_156_);
v___y_125_ = v___x_163_;
v___y_126_ = v___x_162_;
goto v___jp_124_;
}
}
else
{
uint8_t v___x_164_; 
v___x_164_ = lean_unbox(v_a_156_);
lean_dec(v_a_156_);
v___y_125_ = v___x_164_;
v___y_126_ = v___x_158_;
goto v___jp_124_;
}
}
else
{
lean_object* v___x_165_; 
lean_dec(v_a_156_);
lean_inc_ref(v_a_36_);
v___x_165_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_36_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
v___x_167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
v___x_168_ = l_Lean_mkApp3(v___x_167_, v_a_36_, v_b_37_, v_a_166_);
v___x_169_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_35_, v___x_168_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_169_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_170_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_165_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_178_ = lean_ctor_get(v___y_155_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___y_155_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___y_155_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___y_155_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object* v_e_209_, lean_object* v_a_210_, lean_object* v_b_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_209_, v_a_210_, v_b_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec(v_a_212_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0(lean_object* v_cls_227_, lean_object* v_____do__lift_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_toCold_240_; lean_object* v_options_241_; uint8_t v_hasTrace_242_; 
v_toCold_240_ = lean_ctor_get(v___y_237_, 0);
v_options_241_ = lean_ctor_get(v_toCold_240_, 2);
v_hasTrace_242_ = lean_ctor_get_uint8(v_options_241_, sizeof(void*)*1);
if (v_hasTrace_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_cls_227_);
v___x_243_ = lean_box(v_hasTrace_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_245_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_246_ = l_Lean_Name_append(v___x_245_, v_cls_227_);
v___x_247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_228_, v_options_241_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_box(v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___boxed(lean_object* v_cls_250_, lean_object* v_____do__lift_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_250_, v_____do__lift_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v_____do__lift_251_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_env_271_; lean_object* v___x_272_; lean_object* v_toCold_273_; lean_object* v_mctx_274_; lean_object* v_lctx_275_; lean_object* v_options_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_270_ = lean_st_ref_get(v___y_268_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_env_271_);
lean_dec(v___x_270_);
v___x_272_ = lean_st_ref_get(v___y_266_);
v_toCold_273_ = lean_ctor_get(v___y_267_, 0);
v_mctx_274_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_mctx_274_);
lean_dec(v___x_272_);
v_lctx_275_ = lean_ctor_get(v___y_265_, 2);
v_options_276_ = lean_ctor_get(v_toCold_273_, 2);
lean_inc_ref(v_options_276_);
lean_inc_ref(v_lctx_275_);
v___x_277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_277_, 0, v_env_271_);
lean_ctor_set(v___x_277_, 1, v_mctx_274_);
lean_ctor_set(v___x_277_, 2, v_lctx_275_);
lean_ctor_set(v___x_277_, 3, v_options_276_);
v___x_278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_msgData_264_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(lean_object* v_msgData_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msgData_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_286_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_287_; double v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_float_of_nat(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* v_cls_292_, lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_ref_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_346_; 
v_ref_299_ = lean_ctor_get(v___y_296_, 2);
v___x_300_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_346_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_346_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_346_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_traceState_306_; lean_object* v_env_307_; lean_object* v_nextMacroScope_308_; lean_object* v_ngen_309_; lean_object* v_auxDeclNGen_310_; lean_object* v_cache_311_; lean_object* v_recordedDeps_312_; lean_object* v_messages_313_; lean_object* v_infoState_314_; lean_object* v_snapshotTasks_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_345_; 
v___x_305_ = lean_st_ref_take(v___y_297_);
v_traceState_306_ = lean_ctor_get(v___x_305_, 4);
v_env_307_ = lean_ctor_get(v___x_305_, 0);
v_nextMacroScope_308_ = lean_ctor_get(v___x_305_, 1);
v_ngen_309_ = lean_ctor_get(v___x_305_, 2);
v_auxDeclNGen_310_ = lean_ctor_get(v___x_305_, 3);
v_cache_311_ = lean_ctor_get(v___x_305_, 5);
v_recordedDeps_312_ = lean_ctor_get(v___x_305_, 6);
v_messages_313_ = lean_ctor_get(v___x_305_, 7);
v_infoState_314_ = lean_ctor_get(v___x_305_, 8);
v_snapshotTasks_315_ = lean_ctor_get(v___x_305_, 9);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_345_ == 0)
{
v___x_317_ = v___x_305_;
v_isShared_318_ = v_isSharedCheck_345_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_snapshotTasks_315_);
lean_inc(v_infoState_314_);
lean_inc(v_messages_313_);
lean_inc(v_recordedDeps_312_);
lean_inc(v_cache_311_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_310_);
lean_inc(v_ngen_309_);
lean_inc(v_nextMacroScope_308_);
lean_inc(v_env_307_);
lean_dec(v___x_305_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_345_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
uint64_t v_tid_319_; lean_object* v_traces_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_344_; 
v_tid_319_ = lean_ctor_get_uint64(v_traceState_306_, sizeof(void*)*1);
v_traces_320_ = lean_ctor_get(v_traceState_306_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_traceState_306_);
if (v_isSharedCheck_344_ == 0)
{
v___x_322_ = v_traceState_306_;
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_traces_320_);
lean_dec(v_traceState_306_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; double v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_324_ = lean_box(0);
v___x_325_ = lean_box(0);
v___x_326_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
v___x_327_ = 0;
v___x_328_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
v___x_329_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_329_, 0, v_cls_292_);
lean_ctor_set(v___x_329_, 1, v___x_325_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_ctor_set_float(v___x_329_, sizeof(void*)*3, v___x_326_);
lean_ctor_set_float(v___x_329_, sizeof(void*)*3 + 8, v___x_326_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*3 + 16, v___x_327_);
v___x_330_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2));
v___x_331_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v_a_301_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
lean_inc(v_ref_299_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_ref_299_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = l_Lean_PersistentArray_push___redArg(v_traces_320_, v___x_332_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_333_);
v___x_335_ = v___x_322_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_333_);
lean_ctor_set_uint64(v_reuseFailAlloc_343_, sizeof(void*)*1, v_tid_319_);
v___x_335_ = v_reuseFailAlloc_343_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v___x_335_);
v___x_337_ = v___x_317_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_env_307_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_nextMacroScope_308_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_ngen_309_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_auxDeclNGen_310_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_342_, 5, v_cache_311_);
lean_ctor_set(v_reuseFailAlloc_342_, 6, v_recordedDeps_312_);
lean_ctor_set(v_reuseFailAlloc_342_, 7, v_messages_313_);
lean_ctor_set(v_reuseFailAlloc_342_, 8, v_infoState_314_);
lean_ctor_set(v_reuseFailAlloc_342_, 9, v_snapshotTasks_315_);
v___x_337_ = v_reuseFailAlloc_342_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_st_ref_put(v___y_297_, v___x_337_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_324_);
v___x_340_ = v___x_303_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_324_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* v_cls_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_347_, v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_box(0);
v___x_361_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
v___x_362_ = l_Lean_mkConst(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7(void){
_start:
{
lean_object* v_cls_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_cls_370_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_371_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_372_ = l_Lean_Name_append(v___x_371_, v_cls_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__8));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__10));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__12));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* v_e_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
if (lean_obj_tag(v_e_382_) == 7)
{
lean_object* v_binderName_394_; lean_object* v_binderType_395_; lean_object* v_body_396_; uint8_t v_binderInfo_397_; lean_object* v___y_399_; uint8_t v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v_toCold_423_; lean_object* v_inheritedTraceOptions_424_; lean_object* v_cls_425_; uint8_t v___y_427_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___x_532_; lean_object* v_a_533_; uint8_t v___x_534_; 
v_binderName_394_ = lean_ctor_get(v_e_382_, 0);
v_binderType_395_ = lean_ctor_get(v_e_382_, 1);
v_body_396_ = lean_ctor_get(v_e_382_, 2);
v_binderInfo_397_ = lean_ctor_get_uint8(v_e_382_, sizeof(void*)*3 + 8);
v_toCold_423_ = lean_ctor_get(v_a_391_, 0);
v_inheritedTraceOptions_424_ = lean_ctor_get(v_toCold_423_, 11);
v_cls_425_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_532_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_425_, v_inheritedTraceOptions_424_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = lean_unbox(v_a_533_);
lean_dec(v_a_533_);
if (v___x_534_ == 0)
{
v___y_490_ = v_a_383_;
v___y_491_ = v_a_384_;
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
v___y_499_ = v_a_392_;
goto v___jp_489_;
}
else
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_Meta_Grind_updateLastTag(v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref_known(v___x_535_, 1);
lean_inc_ref(v_e_382_);
v___x_536_ = l_Lean_MessageData_ofExpr(v_e_382_);
v___x_537_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_425_, v___x_536_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_dec_ref_known(v___x_537_, 1);
v___y_490_ = v_a_383_;
v___y_491_ = v_a_384_;
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
v___y_499_ = v_a_392_;
goto v___jp_489_;
}
else
{
lean_dec_ref_known(v_e_382_, 3);
return v___x_537_;
}
}
else
{
lean_dec_ref_known(v_e_382_, 3);
return v___x_535_;
}
}
v___jp_398_:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Simp_Result_getProof(v___y_402_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(v___y_401_);
lean_inc_ref(v_binderType_395_);
v___x_413_ = l_Lean_mkApp5(v___x_412_, v_binderType_395_, v___y_399_, v___y_401_, v___y_403_, v_a_411_);
v___x_414_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_382_, v___y_401_, v___x_413_, v___y_400_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
return v___x_414_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v___y_403_);
lean_dec_ref(v___y_401_);
lean_dec_ref(v___y_399_);
lean_dec_ref_known(v_e_382_, 3);
v_a_415_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_410_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_410_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
v___jp_426_:
{
lean_object* v___x_438_; 
lean_inc_ref(v_binderType_395_);
v___x_438_ = l_Lean_Meta_Grind_mkEqTrueProof(v_binderType_395_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_n(v_a_439_, 2);
lean_dec_ref_known(v___x_438_, 1);
lean_inc_ref(v_binderType_395_);
v___x_440_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_395_, v_a_439_);
v___x_441_ = lean_expr_instantiate1(v_body_396_, v___x_440_);
lean_dec_ref(v___x_440_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc(v___y_428_);
v___x_442_ = lean_grind_preprocess(v___x_441_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v_expr_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v_expr_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc_ref(v_expr_444_);
lean_inc_ref(v_body_396_);
lean_inc_ref(v_binderType_395_);
lean_inc(v_binderName_394_);
v___x_445_ = l_Lean_mkLambda(v_binderName_394_, v_binderInfo_397_, v_binderType_395_, v_body_396_);
v___x_446_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_382_, v___y_428_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_box(0);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v_expr_444_);
v___x_449_ = lean_grind_internalize(v_expr_444_, v_a_447_, v___x_448_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_toCold_450_; lean_object* v_options_451_; uint8_t v_hasTrace_452_; 
lean_dec_ref_known(v___x_449_, 1);
v_toCold_450_ = lean_ctor_get(v___y_436_, 0);
v_options_451_ = lean_ctor_get(v_toCold_450_, 2);
v_hasTrace_452_ = lean_ctor_get_uint8(v_options_451_, sizeof(void*)*1);
if (v_hasTrace_452_ == 0)
{
v___y_399_ = v___x_445_;
v___y_400_ = v___y_427_;
v___y_401_ = v_expr_444_;
v___y_402_ = v_a_443_;
v___y_403_ = v_a_439_;
v___y_404_ = v___y_428_;
v___y_405_ = v___y_430_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
goto v___jp_398_;
}
else
{
lean_object* v_inheritedTraceOptions_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_inheritedTraceOptions_453_ = lean_ctor_get(v_toCold_450_, 11);
v___x_454_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__7, &l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
v___x_455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_453_, v_options_451_, v___x_454_);
if (v___x_455_ == 0)
{
v___y_399_ = v___x_445_;
v___y_400_ = v___y_427_;
v___y_401_ = v_expr_444_;
v___y_402_ = v_a_443_;
v___y_403_ = v_a_439_;
v___y_404_ = v___y_428_;
v___y_405_ = v___y_430_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
goto v___jp_398_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Grind_updateLastTag(v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref_known(v___x_456_, 1);
v___x_457_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__9, &l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
lean_inc_ref(v_expr_444_);
v___x_458_ = l_Lean_MessageData_ofExpr(v_expr_444_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__11, &l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_inc_ref(v_e_382_);
v___x_462_ = l_Lean_indentExpr(v_e_382_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_425_, v___x_463_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_dec_ref_known(v___x_464_, 1);
v___y_399_ = v___x_445_;
v___y_400_ = v___y_427_;
v___y_401_ = v_expr_444_;
v___y_402_ = v_a_443_;
v___y_403_ = v_a_439_;
v___y_404_ = v___y_428_;
v___y_405_ = v___y_430_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_435_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
goto v___jp_398_;
}
else
{
lean_dec_ref(v___x_445_);
lean_dec_ref(v_expr_444_);
lean_dec(v_a_443_);
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_382_, 3);
return v___x_464_;
}
}
else
{
lean_dec_ref(v___x_445_);
lean_dec_ref(v_expr_444_);
lean_dec(v_a_443_);
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_382_, 3);
return v___x_456_;
}
}
}
}
else
{
lean_dec_ref(v___x_445_);
lean_dec_ref(v_expr_444_);
lean_dec(v_a_443_);
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_382_, 3);
return v___x_449_;
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___x_445_);
lean_dec_ref(v_expr_444_);
lean_dec(v_a_443_);
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_382_, 3);
v_a_465_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_446_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_446_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_a_439_);
lean_dec_ref_known(v_e_382_, 3);
v_a_473_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_442_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_442_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
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
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref_known(v_e_382_, 3);
v_a_481_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_438_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_438_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
v___jp_489_:
{
uint8_t v___x_500_; 
v___x_500_ = l_Lean_Expr_hasLooseBVars(v_body_396_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_inc_ref(v_body_396_);
lean_inc_ref(v_binderType_395_);
v___x_501_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_382_, v_binderType_395_, v_body_396_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_501_;
}
else
{
uint8_t v___x_502_; lean_object* v___x_503_; 
v___x_502_ = 0;
lean_inc_ref(v_binderType_395_);
v___x_503_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_395_, v___y_490_, v___y_494_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_523_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_523_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; 
v___x_508_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec_ref_known(v_e_382_, 3);
v___x_509_ = lean_box(0);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
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
lean_object* v_toCold_513_; lean_object* v_inheritedTraceOptions_514_; lean_object* v___x_515_; lean_object* v_a_516_; uint8_t v___x_517_; 
lean_del_object(v___x_506_);
v_toCold_513_ = lean_ctor_get(v___y_498_, 0);
v_inheritedTraceOptions_514_ = lean_ctor_get(v_toCold_513_, 11);
v___x_515_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_425_, v_inheritedTraceOptions_514_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_515_);
v___x_517_ = lean_unbox(v_a_516_);
lean_dec(v_a_516_);
if (v___x_517_ == 0)
{
v___y_427_ = v___x_502_;
v___y_428_ = v___y_490_;
v___y_429_ = v___y_491_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
v___y_437_ = v___y_499_;
goto v___jp_426_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Grind_updateLastTag(v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref_known(v___x_518_, 1);
v___x_519_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__13, &l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
lean_inc_ref(v_e_382_);
v___x_520_ = l_Lean_MessageData_ofExpr(v_e_382_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_425_, v___x_521_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_dec_ref_known(v___x_522_, 1);
v___y_427_ = v___x_502_;
v___y_428_ = v___y_490_;
v___y_429_ = v___y_491_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
v___y_437_ = v___y_499_;
goto v___jp_426_;
}
else
{
lean_dec_ref_known(v_e_382_, 3);
return v___x_522_;
}
}
else
{
lean_dec_ref_known(v_e_382_, 3);
return v___x_518_;
}
}
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref_known(v_e_382_, 3);
v_a_524_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_503_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_503_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref(v_e_382_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* v_e_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Meta_Grind_propagateForallPropUp(v_e_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* v_cls_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_553_, v_msg_554_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* v_cls_567_, lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(v_cls_567_, v_msg_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec(v___y_569_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* v_origin_583_, lean_object* v_proof_584_, lean_object* v_kind_585_, lean_object* v_prios_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_593_ = 0;
v___x_594_ = 1;
v___x_595_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v_origin_583_, v___x_592_, v_proof_584_, v_kind_585_, v_prios_586_, v___x_593_, v___x_593_, v___x_594_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_595_) == 0)
{
return v___x_595_;
}
else
{
lean_object* v_a_596_; uint8_t v___y_598_; uint8_t v___x_608_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
v___x_608_ = l_Lean_Exception_isInterrupt(v_a_596_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Exception_isRuntime(v_a_596_);
v___y_598_ = v___x_609_;
goto v___jp_597_;
}
else
{
lean_dec(v_a_596_);
v___y_598_ = v___x_608_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_606_; 
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_607_);
v___x_600_ = v___x_595_;
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
else
{
lean_dec(v___x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_606_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 0);
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
else
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* v_origin_610_, lean_object* v_proof_611_, lean_object* v_kind_612_, lean_object* v_prios_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_610_, v_proof_611_, v_kind_612_, v_prios_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_619_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
if (lean_obj_tag(v_x_621_) == 0)
{
uint8_t v___x_622_; 
v___x_622_ = 1;
return v___x_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
else
{
if (lean_obj_tag(v_x_621_) == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v_head_627_; lean_object* v_tail_628_; uint8_t v___x_629_; 
v_head_625_ = lean_ctor_get(v_x_620_, 0);
v_tail_626_ = lean_ctor_get(v_x_620_, 1);
v_head_627_ = lean_ctor_get(v_x_621_, 0);
v_tail_628_ = lean_ctor_get(v_x_621_, 1);
v___x_629_ = lean_expr_eqv(v_head_625_, v_head_627_);
if (v___x_629_ == 0)
{
return v___x_629_;
}
else
{
v_x_620_ = v_tail_626_;
v_x_621_ = v_tail_628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_631_, v_x_632_);
lean_dec(v_x_632_);
lean_dec(v_x_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* v_thm_x27_635_, lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_639_ == 0)
{
lean_object* v_patterns_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_patterns_640_ = lean_ctor_get(v_thm_x27_635_, 3);
v___x_641_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v___x_642_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_640_, v___x_641_);
if (v___x_642_ == 0)
{
size_t v___x_643_; size_t v___x_644_; 
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_637_, v___x_643_);
v_i_637_ = v___x_644_;
goto _start;
}
else
{
return v___x_642_;
}
}
else
{
uint8_t v___x_646_; 
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* v_thm_x27_647_, lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_647_, v_as_648_, v_i_boxed_651_, v_stop_boxed_652_);
lean_dec_ref(v_as_648_);
lean_dec_ref(v_thm_x27_647_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* v_patternsFoundSoFar_655_, lean_object* v_thm_x27_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_patternsFoundSoFar_655_);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 1;
return v___x_660_;
}
else
{
if (v___x_659_ == 0)
{
return v___x_659_;
}
else
{
size_t v___x_661_; size_t v___x_662_; uint8_t v___x_663_; 
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_658_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_656_, v_patternsFoundSoFar_655_, v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
return v___x_659_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = 0;
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* v_patternsFoundSoFar_665_, lean_object* v_thm_x27_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_665_, v_thm_x27_666_);
lean_dec_ref(v_thm_x27_666_);
lean_dec_ref(v_patternsFoundSoFar_665_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(lean_object* v_proof_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___y_685_; lean_object* v___x_751_; 
lean_inc_ref(v_proof_680_);
v___x_751_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_680_, v_a_682_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_Expr_cleanupAnnotations(v_a_752_);
v___x_754_ = l_Lean_Expr_isApp(v___x_753_);
if (v___x_754_ == 0)
{
lean_dec_ref(v___x_753_);
v___y_685_ = v_a_681_;
goto v___jp_684_;
}
else
{
lean_object* v_arg_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_arg_755_ = lean_ctor_get(v___x_753_, 1);
lean_inc_ref(v_arg_755_);
v___x_756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_753_);
v___x_757_ = l_Lean_Expr_isApp(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec_ref(v___x_756_);
lean_dec_ref(v_arg_755_);
v___y_685_ = v_a_681_;
goto v___jp_684_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_756_);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3));
v___x_760_ = l_Lean_Expr_isConstOf(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
uint8_t v___x_761_; 
v___x_761_ = l_Lean_Expr_isApp(v___x_758_);
if (v___x_761_ == 0)
{
lean_dec_ref(v___x_758_);
lean_dec_ref(v_arg_755_);
v___y_685_ = v_a_681_;
goto v___jp_684_;
}
else
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_758_);
v___x_763_ = l_Lean_Expr_isApp(v___x_762_);
if (v___x_763_ == 0)
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v_arg_755_);
v___y_685_ = v_a_681_;
goto v___jp_684_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_762_);
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6));
v___x_766_ = l_Lean_Expr_isConstOf(v___x_764_, v___x_765_);
lean_dec_ref(v___x_764_);
if (v___x_766_ == 0)
{
lean_dec_ref(v_arg_755_);
v___y_685_ = v_a_681_;
goto v___jp_684_;
}
else
{
lean_dec_ref(v_proof_680_);
v_proof_680_ = v_arg_755_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v___x_758_);
lean_dec_ref(v_proof_680_);
v_proof_680_ = v_arg_755_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_proof_680_);
v_a_769_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_751_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_751_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
v___jp_684_:
{
if (lean_obj_tag(v_proof_680_) == 1)
{
lean_object* v_fvarId_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_fvarId_686_ = lean_ctor_get(v_proof_680_, 0);
lean_inc(v_fvarId_686_);
lean_dec_ref_known(v_proof_680_, 1);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v_fvarId_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v_toGoalState_690_; lean_object* v_ematch_691_; lean_object* v_mvarId_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_proof_680_);
v___x_689_ = lean_st_ref_take(v___y_685_);
v_toGoalState_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref(v_toGoalState_690_);
v_ematch_691_ = lean_ctor_get(v_toGoalState_690_, 12);
lean_inc_ref(v_ematch_691_);
v_mvarId_692_ = lean_ctor_get(v___x_689_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_689_, 0);
lean_dec(v_unused_750_);
v___x_694_ = v___x_689_;
v_isShared_695_ = v_isSharedCheck_749_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_mvarId_692_);
lean_dec(v___x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_749_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_nextDeclIdx_696_; lean_object* v_enodeMap_697_; lean_object* v_exprs_698_; lean_object* v_parents_699_; lean_object* v_congrTable_700_; lean_object* v_appMap_701_; lean_object* v_indicesFound_702_; lean_object* v_newFacts_703_; uint8_t v_inconsistent_704_; lean_object* v_nextIdx_705_; lean_object* v_newRawFacts_706_; lean_object* v_facts_707_; lean_object* v_extThms_708_; lean_object* v_inj_709_; lean_object* v_split_710_; lean_object* v_clean_711_; lean_object* v_sstates_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_747_; 
v_nextDeclIdx_696_ = lean_ctor_get(v_toGoalState_690_, 0);
v_enodeMap_697_ = lean_ctor_get(v_toGoalState_690_, 1);
v_exprs_698_ = lean_ctor_get(v_toGoalState_690_, 2);
v_parents_699_ = lean_ctor_get(v_toGoalState_690_, 3);
v_congrTable_700_ = lean_ctor_get(v_toGoalState_690_, 4);
v_appMap_701_ = lean_ctor_get(v_toGoalState_690_, 5);
v_indicesFound_702_ = lean_ctor_get(v_toGoalState_690_, 6);
v_newFacts_703_ = lean_ctor_get(v_toGoalState_690_, 7);
v_inconsistent_704_ = lean_ctor_get_uint8(v_toGoalState_690_, sizeof(void*)*17);
v_nextIdx_705_ = lean_ctor_get(v_toGoalState_690_, 8);
v_newRawFacts_706_ = lean_ctor_get(v_toGoalState_690_, 9);
v_facts_707_ = lean_ctor_get(v_toGoalState_690_, 10);
v_extThms_708_ = lean_ctor_get(v_toGoalState_690_, 11);
v_inj_709_ = lean_ctor_get(v_toGoalState_690_, 13);
v_split_710_ = lean_ctor_get(v_toGoalState_690_, 14);
v_clean_711_ = lean_ctor_get(v_toGoalState_690_, 15);
v_sstates_712_ = lean_ctor_get(v_toGoalState_690_, 16);
v_isSharedCheck_747_ = !lean_is_exclusive(v_toGoalState_690_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_toGoalState_690_, 12);
lean_dec(v_unused_748_);
v___x_714_ = v_toGoalState_690_;
v_isShared_715_ = v_isSharedCheck_747_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_sstates_712_);
lean_inc(v_clean_711_);
lean_inc(v_split_710_);
lean_inc(v_inj_709_);
lean_inc(v_extThms_708_);
lean_inc(v_facts_707_);
lean_inc(v_newRawFacts_706_);
lean_inc(v_nextIdx_705_);
lean_inc(v_newFacts_703_);
lean_inc(v_indicesFound_702_);
lean_inc(v_appMap_701_);
lean_inc(v_congrTable_700_);
lean_inc(v_parents_699_);
lean_inc(v_exprs_698_);
lean_inc(v_enodeMap_697_);
lean_inc(v_nextDeclIdx_696_);
lean_dec(v_toGoalState_690_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_747_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_thmMap_716_; lean_object* v_gmt_717_; lean_object* v_thms_718_; lean_object* v_newThms_719_; lean_object* v_numInstances_720_; lean_object* v_numDelayedInstances_721_; lean_object* v_num_722_; lean_object* v_preInstances_723_; lean_object* v_nextThmIdx_724_; lean_object* v_matchEqNames_725_; lean_object* v_delayedThmInsts_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_746_; 
v_thmMap_716_ = lean_ctor_get(v_ematch_691_, 0);
v_gmt_717_ = lean_ctor_get(v_ematch_691_, 1);
v_thms_718_ = lean_ctor_get(v_ematch_691_, 2);
v_newThms_719_ = lean_ctor_get(v_ematch_691_, 3);
v_numInstances_720_ = lean_ctor_get(v_ematch_691_, 4);
v_numDelayedInstances_721_ = lean_ctor_get(v_ematch_691_, 5);
v_num_722_ = lean_ctor_get(v_ematch_691_, 6);
v_preInstances_723_ = lean_ctor_get(v_ematch_691_, 7);
v_nextThmIdx_724_ = lean_ctor_get(v_ematch_691_, 8);
v_matchEqNames_725_ = lean_ctor_get(v_ematch_691_, 9);
v_delayedThmInsts_726_ = lean_ctor_get(v_ematch_691_, 10);
v_isSharedCheck_746_ = !lean_is_exclusive(v_ematch_691_);
if (v_isSharedCheck_746_ == 0)
{
v___x_728_ = v_ematch_691_;
v_isShared_729_ = v_isSharedCheck_746_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_delayedThmInsts_726_);
lean_inc(v_matchEqNames_725_);
lean_inc(v_nextThmIdx_724_);
lean_inc(v_preInstances_723_);
lean_inc(v_num_722_);
lean_inc(v_numDelayedInstances_721_);
lean_inc(v_numInstances_720_);
lean_inc(v_newThms_719_);
lean_inc(v_thms_718_);
lean_inc(v_gmt_717_);
lean_inc(v_thmMap_716_);
lean_dec(v_ematch_691_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_746_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_nextThmIdx_724_, v___x_730_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 8, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_thmMap_716_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_gmt_717_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_thms_718_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_newThms_719_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_numInstances_720_);
lean_ctor_set(v_reuseFailAlloc_745_, 5, v_numDelayedInstances_721_);
lean_ctor_set(v_reuseFailAlloc_745_, 6, v_num_722_);
lean_ctor_set(v_reuseFailAlloc_745_, 7, v_preInstances_723_);
lean_ctor_set(v_reuseFailAlloc_745_, 8, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_745_, 9, v_matchEqNames_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 10, v_delayedThmInsts_726_);
v___x_733_ = v_reuseFailAlloc_745_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 12, v___x_733_);
v___x_735_ = v___x_714_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_nextDeclIdx_696_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_enodeMap_697_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_exprs_698_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_parents_699_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_congrTable_700_);
lean_ctor_set(v_reuseFailAlloc_744_, 5, v_appMap_701_);
lean_ctor_set(v_reuseFailAlloc_744_, 6, v_indicesFound_702_);
lean_ctor_set(v_reuseFailAlloc_744_, 7, v_newFacts_703_);
lean_ctor_set(v_reuseFailAlloc_744_, 8, v_nextIdx_705_);
lean_ctor_set(v_reuseFailAlloc_744_, 9, v_newRawFacts_706_);
lean_ctor_set(v_reuseFailAlloc_744_, 10, v_facts_707_);
lean_ctor_set(v_reuseFailAlloc_744_, 11, v_extThms_708_);
lean_ctor_set(v_reuseFailAlloc_744_, 12, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 13, v_inj_709_);
lean_ctor_set(v_reuseFailAlloc_744_, 14, v_split_710_);
lean_ctor_set(v_reuseFailAlloc_744_, 15, v_clean_711_);
lean_ctor_set(v_reuseFailAlloc_744_, 16, v_sstates_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_744_, sizeof(void*)*17, v_inconsistent_704_);
v___x_735_ = v_reuseFailAlloc_744_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_735_);
v___x_737_ = v___x_694_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_mvarId_692_);
v___x_737_ = v_reuseFailAlloc_743_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_738_ = lean_st_ref_put(v___y_685_, v___x_737_);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1));
v___x_740_ = lean_name_append_index_after(v___x_739_, v_nextThmIdx_724_);
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(lean_object* v_proof_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_777_, v_a_778_, v_a_779_);
lean_dec(v_a_779_);
lean_dec(v_a_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(lean_object* v_proof_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_782_, v_a_783_, v_a_790_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(lean_object* v_proof_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(v_proof_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec(v_a_796_);
return v_res_807_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t v_a_808_, lean_object* v_as_809_, size_t v_i_810_, size_t v_stop_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_eq(v_i_810_, v_stop_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_array_uget_borrowed(v_as_809_, v_i_810_);
v___x_814_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_813_, v_a_808_);
if (v___x_814_ == 0)
{
size_t v___x_815_; size_t v___x_816_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_810_, v___x_815_);
v_i_810_ = v___x_816_;
goto _start;
}
else
{
return v___x_814_;
}
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* v_a_819_, lean_object* v_as_820_, lean_object* v_i_821_, lean_object* v_stop_822_){
_start:
{
uint64_t v_a_3837__boxed_823_; size_t v_i_boxed_824_; size_t v_stop_boxed_825_; uint8_t v_res_826_; lean_object* v_r_827_; 
v_a_3837__boxed_823_ = lean_unbox_uint64(v_a_819_);
lean_dec_ref(v_a_819_);
v_i_boxed_824_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_stop_boxed_825_ = lean_unbox_usize(v_stop_822_);
lean_dec(v_stop_822_);
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_3837__boxed_823_, v_as_820_, v_i_boxed_824_, v_stop_boxed_825_);
lean_dec_ref(v_as_820_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* v_proof_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_830_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_893_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_893_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_893_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_893_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
if (lean_obj_tag(v_a_840_) == 1)
{
lean_object* v_val_844_; lean_object* v___x_845_; 
lean_del_object(v___x_842_);
v_val_844_ = lean_ctor_get(v_a_840_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v_a_840_, 1);
lean_inc(v_a_837_);
lean_inc_ref(v_a_836_);
lean_inc(v_a_835_);
lean_inc_ref(v_a_834_);
v___x_845_ = lean_infer_type(v_proof_828_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = l_Lean_Meta_Grind_getAnchor(v_a_846_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_871_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_871_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_871_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_871_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_array_get_size(v_val_844_);
v___x_854_ = lean_nat_dec_lt(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_a_848_);
lean_dec(v_val_844_);
v___x_855_ = lean_box(v___x_854_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_855_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
if (v___x_854_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_a_848_);
lean_dec(v_val_844_);
v___x_859_ = lean_box(v___x_854_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_859_);
v___x_861_ = v___x_850_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
size_t v___x_863_; size_t v___x_864_; uint64_t v___x_865_; uint8_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_853_);
v___x_865_ = lean_unbox_uint64(v_a_848_);
lean_dec(v_a_848_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_865_, v_val_844_, v___x_863_, v___x_864_);
lean_dec(v_val_844_);
v___x_867_ = lean_box(v___x_866_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_867_);
v___x_869_ = v___x_850_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_val_844_);
v_a_872_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_847_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_847_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_val_844_);
v_a_880_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_845_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_845_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_a_840_);
lean_dec_ref(v_proof_828_);
v___x_888_ = 1;
v___x_889_ = lean_box(v___x_888_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_889_);
v___x_891_ = v___x_842_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_proof_828_);
v_a_894_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_839_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_839_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* v_proof_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* v_a_914_, lean_object* v_as_915_, size_t v_sz_916_, size_t v_i_917_, lean_object* v_b_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_a_931_; uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_917_, v_sz_916_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec(v_a_914_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_b_918_);
return v___x_936_;
}
else
{
lean_object* v_a_937_; uint8_t v___x_938_; 
v_a_937_ = lean_array_uget_borrowed(v_as_915_, v_i_917_);
v___x_938_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_b_918_, v_a_937_);
if (v___x_938_ == 0)
{
v_a_931_ = v_b_918_;
goto v___jp_930_;
}
else
{
lean_object* v___x_939_; 
lean_inc(v_a_914_);
lean_inc(v_a_937_);
v___x_939_ = l_Lean_Meta_Grind_activateTheorem(v_a_937_, v_a_914_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_patterns_940_; lean_object* v___x_941_; 
lean_dec_ref_known(v___x_939_, 1);
v_patterns_940_ = lean_ctor_get(v_a_937_, 3);
lean_inc(v_patterns_940_);
v___x_941_ = lean_array_push(v_b_918_, v_patterns_940_);
v_a_931_ = v___x_941_;
goto v___jp_930_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_b_918_);
lean_dec(v_a_914_);
v_a_942_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_939_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
v___jp_930_:
{
size_t v___x_932_; size_t v___x_933_; 
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_917_, v___x_932_);
v_i_917_ = v___x_933_;
v_b_918_ = v_a_931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* v_a_950_, lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_967_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_950_, v_as_951_, v_sz_boxed_966_, v_i_boxed_967_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v_as_951_);
return v_res_968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
lean_inc_ref(v_e_976_);
v___x_988_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_n(v_a_989_, 2);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_a_989_, v_a_977_, v_a_984_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
lean_inc_ref(v_e_976_);
v___x_992_ = l_Lean_Meta_mkOfEqTrueCore(v_e_976_, v_a_989_);
lean_inc_ref(v___x_992_);
v___x_993_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v___x_992_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1173_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1173_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1173_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v___x_999_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1003_; lean_object* v_toGoalState_1004_; lean_object* v_ematch_1005_; lean_object* v_newThms_1006_; lean_object* v_size_1007_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___x_1056_; 
v___x_1003_ = lean_st_ref_get(v_a_977_);
v_toGoalState_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_ref(v_toGoalState_1004_);
lean_dec(v___x_1003_);
v_ematch_1005_ = lean_ctor_get(v_toGoalState_1004_, 12);
lean_inc_ref(v_ematch_1005_);
lean_dec_ref(v_toGoalState_1004_);
v_newThms_1006_ = lean_ctor_get(v_ematch_1005_, 3);
lean_inc_ref(v_newThms_1006_);
lean_dec_ref(v_ematch_1005_);
v_size_1007_ = lean_ctor_get(v_newThms_1006_, 2);
lean_inc(v_size_1007_);
lean_dec_ref(v_newThms_1006_);
v___x_1056_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_976_, v_a_977_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2));
v___x_1059_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v_a_979_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v_patternsFoundSoFar_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___x_1119_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_n(v_a_1060_, 2);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_unsigned_to_nat(1000u);
v___x_1062_ = 0;
lean_inc_ref(v___x_992_);
lean_inc(v_a_991_);
v___x_1119_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(v_a_991_, v___x_1058_, v___x_992_, v___x_1061_, v_a_1060_, v___x_1062_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v_sz_1121_ = lean_array_size(v_a_1120_);
v___x_1122_ = ((size_t)0ULL);
lean_inc(v_a_1057_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_1057_, v_a_1120_, v_sz_1121_, v___x_1122_, v___x_1058_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_box(6);
lean_inc(v_a_1060_);
lean_inc_ref(v___x_992_);
lean_inc(v_a_991_);
v___x_1126_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_991_, v___x_992_, v___x_1125_, v_a_1060_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
if (lean_obj_tag(v_a_1127_) == 1)
{
lean_object* v_val_1128_; uint8_t v___x_1129_; 
v_val_1128_ = lean_ctor_get(v_a_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v_a_1127_, 1);
v___x_1129_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_a_1124_, v_val_1128_);
if (v___x_1129_ == 0)
{
lean_dec(v_val_1128_);
v_patternsFoundSoFar_1094_ = v_a_1124_;
v___y_1095_ = v_a_977_;
v___y_1096_ = v_a_978_;
v___y_1097_ = v_a_979_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1130_; 
lean_inc(v_a_1057_);
lean_inc(v_val_1128_);
v___x_1130_ = l_Lean_Meta_Grind_activateTheorem(v_val_1128_, v_a_1057_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_patterns_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1130_, 1);
v_patterns_1131_ = lean_ctor_get(v_val_1128_, 3);
lean_inc(v_patterns_1131_);
lean_dec(v_val_1128_);
v___x_1132_ = lean_array_push(v_a_1124_, v_patterns_1131_);
v_patternsFoundSoFar_1094_ = v___x_1132_;
v___y_1095_ = v_a_977_;
v___y_1096_ = v_a_978_;
v___y_1097_ = v_a_979_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
goto v___jp_1093_;
}
else
{
lean_dec(v_val_1128_);
lean_dec(v_a_1124_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
return v___x_1130_;
}
}
}
else
{
lean_dec(v_a_1127_);
v_patternsFoundSoFar_1094_ = v_a_1124_;
v___y_1095_ = v_a_977_;
v___y_1096_ = v_a_978_;
v___y_1097_ = v_a_979_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
goto v___jp_1093_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1124_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1133_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1126_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1126_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1141_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1123_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1123_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1149_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1119_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1119_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
v___jp_1063_:
{
lean_object* v___x_1074_; lean_object* v_toGoalState_1075_; lean_object* v_ematch_1076_; lean_object* v_newThms_1077_; lean_object* v_size_1078_; uint8_t v___x_1079_; 
v___x_1074_ = lean_st_ref_get(v___y_1064_);
v_toGoalState_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_toGoalState_1075_);
lean_dec(v___x_1074_);
v_ematch_1076_ = lean_ctor_get(v_toGoalState_1075_, 12);
lean_inc_ref(v_ematch_1076_);
lean_dec_ref(v_toGoalState_1075_);
v_newThms_1077_ = lean_ctor_get(v_ematch_1076_, 3);
lean_inc_ref(v_newThms_1077_);
lean_dec_ref(v_ematch_1076_);
v_size_1078_ = lean_ctor_get(v_newThms_1077_, 2);
lean_inc(v_size_1078_);
lean_dec_ref(v_newThms_1077_);
v___x_1079_ = lean_nat_dec_eq(v_size_1078_, v_size_1007_);
lean_dec(v_size_1078_);
if (v___x_1079_ == 0)
{
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
v___y_1009_ = v___y_1064_;
v___y_1010_ = v___y_1068_;
v___y_1011_ = v___y_1069_;
v___y_1012_ = v___y_1070_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
goto v___jp_1008_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3));
v___x_1081_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_991_, v___x_992_, v___x_1080_, v_a_1060_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
if (lean_obj_tag(v_a_1082_) == 1)
{
lean_object* v_val_1083_; lean_object* v___x_1084_; 
v_val_1083_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_a_1082_, 1);
v___x_1084_ = l_Lean_Meta_Grind_activateTheorem(v_val_1083_, v_a_1057_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_dec_ref_known(v___x_1084_, 1);
v___y_1009_ = v___y_1064_;
v___y_1010_ = v___y_1068_;
v___y_1011_ = v___y_1069_;
v___y_1012_ = v___y_1070_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
goto v___jp_1008_;
}
else
{
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v_e_976_);
return v___x_1084_;
}
}
else
{
lean_dec(v_a_1082_);
lean_dec(v_a_1057_);
v___y_1009_ = v___y_1064_;
v___y_1010_ = v___y_1068_;
v___y_1011_ = v___y_1069_;
v___y_1012_ = v___y_1070_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
goto v___jp_1008_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v_e_976_);
v_a_1085_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1081_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1081_);
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
}
v___jp_1093_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(7);
lean_inc(v_a_1060_);
lean_inc_ref(v___x_992_);
lean_inc(v_a_991_);
v___x_1106_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_991_, v___x_992_, v___x_1105_, v_a_1060_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
if (lean_obj_tag(v_a_1107_) == 1)
{
lean_object* v_val_1108_; uint8_t v___x_1109_; 
v_val_1108_ = lean_ctor_get(v_a_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_a_1107_, 1);
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_1094_, v_val_1108_);
lean_dec_ref(v_patternsFoundSoFar_1094_);
if (v___x_1109_ == 0)
{
lean_dec(v_val_1108_);
v___y_1064_ = v___y_1095_;
v___y_1065_ = v___y_1096_;
v___y_1066_ = v___y_1097_;
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1110_; 
lean_inc(v_a_1057_);
v___x_1110_ = l_Lean_Meta_Grind_activateTheorem(v_val_1108_, v_a_1057_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1064_ = v___y_1095_;
v___y_1065_ = v___y_1096_;
v___y_1066_ = v___y_1097_;
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
goto v___jp_1063_;
}
else
{
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
return v___x_1110_;
}
}
}
else
{
lean_dec(v_a_1107_);
lean_dec_ref(v_patternsFoundSoFar_1094_);
v___y_1064_ = v___y_1095_;
v___y_1065_ = v___y_1096_;
v___y_1066_ = v___y_1097_;
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
goto v___jp_1063_;
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_patternsFoundSoFar_1094_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1111_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1106_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1106_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_a_1057_);
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1157_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1059_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1059_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_size_1007_);
lean_del_object(v___x_996_);
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1165_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1056_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1056_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
v___jp_1008_:
{
lean_object* v___x_1016_; lean_object* v_toGoalState_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1054_; 
v___x_1016_ = lean_st_ref_get(v___y_1009_);
v_toGoalState_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1016_, 1);
lean_dec(v_unused_1055_);
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1054_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_toGoalState_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1054_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_ematch_1021_; lean_object* v_newThms_1022_; lean_object* v_size_1023_; uint8_t v___x_1024_; 
v_ematch_1021_ = lean_ctor_get(v_toGoalState_1017_, 12);
lean_inc_ref(v_ematch_1021_);
lean_dec_ref(v_toGoalState_1017_);
v_newThms_1022_ = lean_ctor_get(v_ematch_1021_, 3);
lean_inc_ref(v_newThms_1022_);
lean_dec_ref(v_ematch_1021_);
v_size_1023_ = lean_ctor_get(v_newThms_1022_, 2);
lean_inc(v_size_1023_);
lean_dec_ref(v_newThms_1022_);
v___x_1024_ = lean_nat_dec_eq(v_size_1023_, v_size_1007_);
lean_dec(v_size_1007_);
lean_dec(v_size_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_del_object(v___x_1019_);
lean_dec_ref(v_e_976_);
v___x_1025_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1025_);
v___x_1027_ = v___x_996_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_del_object(v___x_996_);
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
v___x_1030_ = l_Lean_indentExpr(v_e_976_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 7);
lean_ctor_set(v___x_1019_, 1, v___x_1030_);
lean_ctor_set(v___x_1019_, 0, v___x_1029_);
v___x_1032_ = v___x_1019_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1010_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v_verbose_1038_; 
v_verbose_1038_ = lean_ctor_get_uint8(v_a_1034_, 0);
lean_dec(v_a_1034_);
if (v_verbose_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec_ref(v___x_1032_);
v___x_1039_ = lean_box(0);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
else
{
lean_object* v___x_1043_; 
lean_del_object(v___x_1036_);
v___x_1043_ = l_Lean_Meta_Sym_reportIssue(v___x_1032_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___x_1032_);
v_a_1045_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1033_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1033_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
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
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v___x_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_e_976_);
v_a_1174_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_993_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_993_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_a_989_);
lean_dec_ref(v_e_976_);
v_a_1182_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_990_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_990_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_e_976_);
v_a_1190_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_988_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_988_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec(v_a_1199_);
return v_res_1210_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_1217_ = l_Lean_Name_append(v___x_1216_, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__3));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(0);
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__10));
v___x_1236_ = l_Lean_mkConst(v___x_1235_, v___x_1234_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__13));
v___x_1244_ = l_Lean_mkConst(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
if (lean_obj_tag(v_e_1245_) == 7)
{
lean_object* v_binderName_1257_; lean_object* v_binderType_1258_; lean_object* v_body_1259_; uint8_t v_binderInfo_1260_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___x_1369_; 
v_binderName_1257_ = lean_ctor_get(v_e_1245_, 0);
v_binderType_1258_ = lean_ctor_get(v_e_1245_, 1);
v_body_1259_ = lean_ctor_get(v_e_1245_, 2);
v_binderInfo_1260_ = lean_ctor_get_uint8(v_e_1245_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_1245_);
v___x_1369_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1245_, v_a_1246_, v_a_1250_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_unbox(v_a_1370_);
lean_dec(v_a_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_inc_ref(v_e_1245_);
v___x_1372_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1245_, v_a_1246_, v_a_1250_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1457_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1457_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1457_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref_known(v_e_1245_, 3);
v___x_1378_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; 
lean_del_object(v___x_1375_);
lean_inc_ref(v_e_1245_);
v___x_1382_ = l_Lean_Meta_Grind_eqResolution(v_e_1245_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
if (lean_obj_tag(v_a_1383_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1448_; 
v_val_1384_ = lean_ctor_get(v_a_1383_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_a_1383_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1386_ = v_a_1383_;
v_isShared_1387_ = v_isSharedCheck_1448_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v_a_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1448_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_fst_1388_; lean_object* v_snd_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1447_; 
v_fst_1388_ = lean_ctor_get(v_val_1384_, 0);
v_snd_1389_ = lean_ctor_get(v_val_1384_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_val_1384_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1391_ = v_val_1384_;
v_isShared_1392_ = v_isSharedCheck_1447_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snd_1389_);
lean_inc(v_fst_1388_);
lean_dec(v_val_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1447_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v_toCold_1431_; lean_object* v_options_1432_; uint8_t v_hasTrace_1433_; 
v_toCold_1431_ = lean_ctor_get(v_a_1254_, 0);
v_options_1432_ = lean_ctor_get(v_toCold_1431_, 2);
v_hasTrace_1433_ = lean_ctor_get_uint8(v_options_1432_, sizeof(void*)*1);
if (v_hasTrace_1433_ == 0)
{
lean_del_object(v___x_1391_);
v___y_1394_ = v_a_1246_;
v___y_1395_ = v_a_1247_;
v___y_1396_ = v_a_1248_;
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
goto v___jp_1393_;
}
else
{
lean_object* v_inheritedTraceOptions_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_inheritedTraceOptions_1434_ = lean_ctor_get(v_toCold_1431_, 11);
v___x_1435_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__2, &l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
v___x_1437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1434_, v_options_1432_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_del_object(v___x_1391_);
v___y_1394_ = v_a_1246_;
v___y_1395_ = v_a_1247_;
v___y_1396_ = v_a_1248_;
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Meta_Grind_updateLastTag(v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec_ref_known(v___x_1438_, 1);
lean_inc_ref(v_e_1245_);
v___x_1439_ = l_Lean_MessageData_ofExpr(v_e_1245_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__4, &l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 7);
lean_ctor_set(v___x_1391_, 1, v___x_1440_);
lean_ctor_set(v___x_1391_, 0, v___x_1439_);
v___x_1442_ = v___x_1391_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_inc(v_fst_1388_);
v___x_1443_ = l_Lean_MessageData_ofExpr(v_fst_1388_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v___x_1435_, v___x_1444_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_dec_ref_known(v___x_1445_, 1);
v___y_1394_ = v_a_1246_;
v___y_1395_ = v_a_1247_;
v___y_1396_ = v_a_1248_;
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
goto v___jp_1393_;
}
else
{
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec_ref_known(v_e_1245_, 3);
return v___x_1445_;
}
}
}
else
{
lean_del_object(v___x_1391_);
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec_ref_known(v_e_1245_, 3);
return v___x_1438_;
}
}
}
v___jp_1393_:
{
lean_object* v___x_1404_; 
lean_inc_ref(v_e_1245_);
v___x_1404_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1245_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
lean_inc_ref(v_e_1245_);
v___x_1406_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1245_, v_a_1405_);
v___x_1407_ = l_Lean_Expr_app___override(v_snd_1389_, v___x_1406_);
v___x_1408_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1245_, v___y_1394_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
lean_inc_ref(v_e_1245_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 4);
lean_ctor_set(v___x_1386_, 0, v_e_1245_);
v___x_1411_ = v___x_1386_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_e_1245_);
v___x_1411_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_box(1);
v___x_1413_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1407_, v_fst_1388_, v_a_1409_, v___x_1411_, v___x_1412_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
v___y_1315_ = v___y_1394_;
v___y_1316_ = v___y_1395_;
v___y_1317_ = v___y_1396_;
v___y_1318_ = v___y_1397_;
v___y_1319_ = v___y_1398_;
v___y_1320_ = v___y_1399_;
v___y_1321_ = v___y_1400_;
v___y_1322_ = v___y_1401_;
v___y_1323_ = v___y_1402_;
v___y_1324_ = v___y_1403_;
goto v___jp_1314_;
}
else
{
lean_dec_ref_known(v_e_1245_, 3);
return v___x_1413_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___x_1407_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1415_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1408_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1408_);
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
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_del_object(v___x_1386_);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1423_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1404_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1404_);
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
}
}
}
else
{
lean_dec(v_a_1383_);
v___y_1315_ = v_a_1246_;
v___y_1316_ = v_a_1247_;
v___y_1317_ = v_a_1248_;
v___y_1318_ = v_a_1249_;
v___y_1319_ = v_a_1250_;
v___y_1320_ = v_a_1251_;
v___y_1321_ = v_a_1252_;
v___y_1322_ = v_a_1253_;
v___y_1323_ = v_a_1254_;
v___y_1324_ = v_a_1255_;
goto v___jp_1314_;
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1449_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1382_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1382_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1458_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1372_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1372_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v___x_1466_; 
lean_inc_ref(v_binderType_1258_);
v___x_1466_ = l_Lean_Meta_isProp(v_binderType_1258_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; uint8_t v___x_1513_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1513_ = l_Lean_Expr_hasLooseBVars(v_body_1259_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_unbox(v_a_1467_);
lean_dec(v_a_1467_);
if (v___x_1514_ == 0)
{
goto v___jp_1468_;
}
else
{
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; 
lean_inc_ref(v_body_1259_);
lean_inc_ref(v_binderType_1258_);
v___x_1515_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc_n(v_a_1516_, 2);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__11, &l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
lean_inc_ref(v_body_1259_);
lean_inc_ref_n(v_binderType_1258_, 2);
v___x_1518_ = l_Lean_mkApp3(v___x_1517_, v_binderType_1258_, v_body_1259_, v_a_1516_);
v___x_1519_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_binderType_1258_, v___x_1518_, v_a_1246_, v_a_1248_, v_a_1250_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref_known(v___x_1519_, 1);
v___x_1520_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__14, &l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
lean_inc_ref(v_body_1259_);
v___x_1521_ = l_Lean_mkApp3(v___x_1520_, v_binderType_1258_, v_body_1259_, v_a_1516_);
v___x_1522_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_body_1259_, v___x_1521_, v_a_1246_, v_a_1248_, v_a_1250_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1522_;
}
else
{
lean_dec(v_a_1516_);
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
return v___x_1519_;
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
v_a_1523_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1515_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1515_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
goto v___jp_1468_;
}
}
}
else
{
lean_dec(v_a_1467_);
goto v___jp_1468_;
}
v___jp_1468_:
{
lean_object* v___x_1469_; 
lean_inc_ref(v_binderType_1258_);
v___x_1469_ = l_Lean_Meta_getLevel(v_binderType_1258_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1470_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
lean_inc_ref(v___x_1473_);
v___x_1474_ = l_Lean_mkConst(v___x_1471_, v___x_1473_);
lean_inc_ref(v_body_1259_);
v___x_1475_ = l_Lean_mkNot(v_body_1259_);
lean_inc_ref_n(v_binderType_1258_, 2);
lean_inc(v_binderName_1257_);
v___x_1476_ = l_Lean_mkLambda(v_binderName_1257_, v_binderInfo_1260_, v_binderType_1258_, v___x_1475_);
v___x_1477_ = l_Lean_mkAppB(v___x_1474_, v_binderType_1258_, v___x_1476_);
lean_inc_ref(v_e_1245_);
v___x_1478_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
v___x_1480_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__8));
v___x_1481_ = l_Lean_mkConst(v___x_1480_, v___x_1473_);
lean_inc_ref(v_body_1259_);
lean_inc_ref_n(v_binderType_1258_, 2);
lean_inc(v_binderName_1257_);
v___x_1482_ = l_Lean_mkLambda(v_binderName_1257_, v_binderInfo_1260_, v_binderType_1258_, v_body_1259_);
v___x_1483_ = l_Lean_mkApp3(v___x_1481_, v_binderType_1258_, v___x_1482_, v_a_1479_);
v___x_1484_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1486_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_e_1245_);
v___x_1487_ = lean_box(1);
v___x_1488_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1483_, v___x_1477_, v_a_1485_, v___x_1486_, v___x_1487_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v___x_1483_);
lean_dec_ref(v___x_1477_);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1489_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1484_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1484_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v___x_1477_);
lean_dec_ref_known(v___x_1473_, 2);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1497_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1478_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1478_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1505_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1469_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1469_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1531_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1466_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1466_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1539_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1369_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1369_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
v___jp_1261_:
{
if (lean_obj_tag(v___y_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1305_; 
v_a_1273_ = lean_ctor_get(v___y_1272_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___y_1272_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1275_ = v___y_1272_;
v_isShared_1276_ = v_isSharedCheck_1305_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___y_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1305_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint8_t v___x_1277_; 
v___x_1277_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
lean_dec_ref_known(v_e_1245_, 3);
v___x_1278_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
lean_object* v___x_1282_; 
lean_del_object(v___x_1275_);
v___x_1282_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1245_, v___y_1268_, v___y_1265_, v___y_1266_, v___y_1271_, v___y_1263_, v___y_1262_, v___y_1267_, v___y_1270_, v___y_1264_, v___y_1269_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
lean_inc_ref(v_body_1259_);
v___x_1284_ = l_Lean_Meta_Grind_mkEqFalseProof(v_body_1259_, v___y_1268_, v___y_1265_, v___y_1266_, v___y_1271_, v___y_1263_, v___y_1262_, v___y_1267_, v___y_1270_, v___y_1264_, v___y_1269_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_binderType_1258_);
v___x_1287_ = l_Lean_mkApp4(v___x_1286_, v_binderType_1258_, v_body_1259_, v_a_1283_, v_a_1285_);
v___x_1288_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_binderType_1258_, v___x_1287_, v___y_1268_, v___y_1266_, v___y_1263_, v___y_1267_, v___y_1270_, v___y_1264_, v___y_1269_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_a_1283_);
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
v_a_1289_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1284_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1284_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
v_a_1297_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1282_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1282_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1306_ = lean_ctor_get(v___y_1272_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___y_1272_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___y_1272_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___y_1272_);
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
}
v___jp_1314_:
{
uint8_t v___x_1325_; 
v___x_1325_ = l_Lean_Expr_hasLooseBVars(v_body_1259_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_inc_ref(v_body_1259_);
lean_inc_ref(v_binderType_1258_);
v___x_1326_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_1259_, v___y_1315_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1340_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1340_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1340_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_unbox(v_a_1327_);
lean_dec(v_a_1327_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
lean_dec_ref_known(v_e_1245_, 3);
v___x_1332_ = lean_box(0);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1332_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1336_; 
lean_del_object(v___x_1329_);
lean_inc_ref(v_body_1259_);
v___x_1336_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_1259_, v___y_1315_, v___y_1319_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; uint8_t v___x_1338_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
v___x_1338_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1338_ == 0)
{
v___y_1262_ = v___y_1320_;
v___y_1263_ = v___y_1319_;
v___y_1264_ = v___y_1323_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1321_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1324_;
v___y_1270_ = v___y_1322_;
v___y_1271_ = v___y_1318_;
v___y_1272_ = v___x_1336_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1336_, 1);
lean_inc_ref(v_binderType_1258_);
v___x_1339_ = l_Lean_Meta_isProp(v_binderType_1258_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
v___y_1262_ = v___y_1320_;
v___y_1263_ = v___y_1319_;
v___y_1264_ = v___y_1323_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1321_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1324_;
v___y_1270_ = v___y_1322_;
v___y_1271_ = v___y_1318_;
v___y_1272_ = v___x_1339_;
goto v___jp_1261_;
}
}
else
{
v___y_1262_ = v___y_1320_;
v___y_1263_ = v___y_1319_;
v___y_1264_ = v___y_1323_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1321_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1324_;
v___y_1270_ = v___y_1322_;
v___y_1271_ = v___y_1318_;
v___y_1272_ = v___x_1336_;
goto v___jp_1261_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_body_1259_);
lean_dec_ref(v_binderType_1258_);
lean_dec_ref_known(v_e_1245_, 3);
v_a_1341_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1326_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1326_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v___x_1349_; 
lean_inc_ref(v_binderType_1258_);
v___x_1349_ = l_Lean_Meta_isProp(v_binderType_1258_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1360_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1360_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_unbox(v_a_1350_);
lean_dec(v_a_1350_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
lean_del_object(v___x_1352_);
v___x_1355_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1245_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec_ref_known(v_e_1245_, 3);
v___x_1356_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1356_);
v___x_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref_known(v_e_1245_, 3);
v_a_1361_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1349_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1349_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref(v_e_1245_);
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* v_e_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Meta_Grind_propagateForallPropDown(v_e_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec(v_a_1550_);
return v_res_1561_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1567_ = l_Lean_mkConst(v___x_1566_, v___x_1565_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = l_Lean_Expr_bvar___override(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* v_e_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1591_; 
lean_inc_ref(v_e_1576_);
v___x_1591_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1576_, v_a_1577_, v_a_1581_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1646_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1646_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1646_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_unbox(v_a_1592_);
lean_dec(v_a_1592_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_dec_ref(v_e_1576_);
v___x_1597_ = lean_box(0);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
else
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
lean_del_object(v___x_1594_);
lean_inc_ref(v_e_1576_);
v___x_1601_ = l_Lean_Expr_cleanupAnnotations(v_e_1576_);
v___x_1602_ = l_Lean_Expr_isApp(v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v___x_1601_);
lean_dec_ref(v_e_1576_);
goto v___jp_1588_;
}
else
{
lean_object* v_arg_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_arg_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc_ref(v_arg_1603_);
v___x_1604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1601_);
v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
if (v___x_1605_ == 0)
{
lean_dec_ref(v___x_1604_);
lean_dec_ref(v_arg_1603_);
lean_dec_ref(v_e_1576_);
goto v___jp_1588_;
}
else
{
lean_object* v_arg_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_arg_1606_ = lean_ctor_get(v___x_1604_, 1);
lean_inc_ref(v_arg_1606_);
v___x_1607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
v___x_1608_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1609_ = l_Lean_Expr_isConstOf(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v___x_1607_);
lean_dec_ref(v_arg_1606_);
lean_dec_ref(v_arg_1603_);
lean_dec_ref(v_e_1576_);
goto v___jp_1588_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1610_ = l_Lean_Expr_constLevels_x21(v___x_1607_);
lean_dec_ref(v___x_1607_);
v___x_1611_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
v___x_1612_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
lean_inc_ref(v_arg_1603_);
v___x_1613_ = l_Lean_Expr_app___override(v_arg_1603_, v___x_1612_);
v___x_1614_ = l_Lean_Expr_headBeta(v___x_1613_);
v___x_1615_ = l_Lean_Expr_app___override(v___x_1611_, v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
v___x_1617_ = 0;
lean_inc_ref(v_arg_1606_);
v___x_1618_ = l_Lean_mkForall(v___x_1616_, v___x_1617_, v_arg_1606_, v___x_1615_);
lean_inc_ref(v_e_1576_);
v___x_1619_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
v___x_1622_ = l_Lean_mkConst(v___x_1621_, v___x_1610_);
lean_inc_ref(v_e_1576_);
v___x_1623_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1576_, v_a_1620_);
v___x_1624_ = l_Lean_mkApp3(v___x_1622_, v_arg_1606_, v_arg_1603_, v___x_1623_);
v___x_1625_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_e_1576_);
v___x_1628_ = lean_box(1);
v___x_1629_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1624_, v___x_1618_, v_a_1626_, v___x_1627_, v___x_1628_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
return v___x_1629_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___x_1624_);
lean_dec_ref(v___x_1618_);
lean_dec_ref(v_e_1576_);
v_a_1630_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1625_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1625_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___x_1618_);
lean_dec(v___x_1610_);
lean_dec_ref(v_arg_1606_);
lean_dec_ref(v_arg_1603_);
lean_dec_ref(v_e_1576_);
v_a_1638_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1619_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1619_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
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
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_e_1576_);
v_a_1647_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1591_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1591_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Meta_Grind_propagateExistsDown(v_e_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_a_1656_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1670_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
v___x_1671_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1669_, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9____boxed(lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
return v_res_1673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_1682_ = l_Lean_mkConst(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* v_e_1683_){
_start:
{
if (lean_obj_tag(v_e_1683_) == 7)
{
lean_object* v_binderName_1684_; lean_object* v_binderType_1685_; lean_object* v_body_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_binderName_1684_ = lean_ctor_get(v_e_1683_, 0);
v_binderType_1685_ = lean_ctor_get(v_e_1683_, 1);
v_body_1686_ = lean_ctor_get(v_e_1683_, 2);
lean_inc_ref(v_body_1686_);
lean_inc_ref(v_binderType_1685_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_binderType_1685_);
lean_ctor_set(v___x_1687_, 1, v_body_1686_);
lean_inc(v_binderName_1684_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_binderName_1684_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = l_Lean_Expr_isAppOfArity(v_e_1683_, v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
v___x_1695_ = l_Lean_Expr_appArg_x21(v_e_1683_);
v___x_1696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1694_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* v_e_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_e_1700_);
lean_dec_ref(v_e_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* v_fst_1702_, lean_object* v_a_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_expr_instantiate1(v_fst_1702_, v_a_1703_);
v___x_1713_ = l_Lean_Meta_getLevel(v___x_1712_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* v_fst_1714_, lean_object* v_a_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Meta_Grind_simpForall___lam__0(v_fst_1714_, v_a_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v_a_1715_);
lean_dec_ref(v_fst_1714_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
v___x_1735_ = lean_apply_9(v_k_1725_, v_b_1729_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, lean_box(0));
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* v_name_1747_, uint8_t v_bi_1748_, lean_object* v_type_1749_, lean_object* v_k_1750_, uint8_t v_kind_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___f_1760_; lean_object* v___x_1761_; 
lean_inc(v___y_1754_);
lean_inc_ref(v___y_1753_);
lean_inc(v___y_1752_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1760_, 0, v_k_1750_);
lean_closure_set(v___f_1760_, 1, v___y_1752_);
lean_closure_set(v___f_1760_, 2, v___y_1753_);
lean_closure_set(v___f_1760_, 3, v___y_1754_);
v___x_1761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1747_, v_bi_1748_, v_type_1749_, v___f_1760_, v_kind_1751_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1761_) == 0)
{
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_1770_, lean_object* v_bi_1771_, lean_object* v_type_1772_, lean_object* v_k_1773_, lean_object* v_kind_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
uint8_t v_bi_boxed_1783_; uint8_t v_kind_boxed_1784_; lean_object* v_res_1785_; 
v_bi_boxed_1783_ = lean_unbox(v_bi_1771_);
v_kind_boxed_1784_ = lean_unbox(v_kind_1774_);
v_res_1785_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1770_, v_bi_boxed_1783_, v_type_1772_, v_k_1773_, v_kind_boxed_1784_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* v_name_1786_, lean_object* v_type_1787_, lean_object* v_k_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = 0;
v___x_1798_ = 0;
v___x_1799_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1786_, v___x_1797_, v_type_1787_, v_k_1788_, v___x_1798_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* v_name_1800_, lean_object* v_type_1801_, lean_object* v_k_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_1800_, v_type_1801_, v_k_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
return v_res_1811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__13(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_1840_ = l_Lean_mkConst(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__16(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__15));
v___x_1848_ = l_Lean_mkConst(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_box(0);
v___x_1860_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__20));
v___x_1861_ = l_Lean_mkConst(v___x_1860_, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(0);
v___x_1868_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__23));
v___x_1869_ = l_Lean_mkConst(v___x_1868_, v___x_1867_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__26));
v___x_1877_ = l_Lean_mkConst(v___x_1876_, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_box(0);
v___x_1884_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__29));
v___x_1885_ = l_Lean_mkConst(v___x_1884_, v___x_1883_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__33(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_box(0);
v___x_1891_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__32));
v___x_1892_ = l_Lean_mkConst(v___x_1891_, v___x_1890_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__36(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__35));
v___x_1900_ = l_Lean_mkConst(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__37(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Lean_Level_ofNat(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__38(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__37, &l_Lean_Meta_Grind_simpForall___closed__37_once, _init_l_Lean_Meta_Grind_simpForall___closed__37);
v___x_1904_ = l_Lean_mkSort(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__41(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_box(0);
v___x_1909_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__40));
v___x_1910_ = l_Lean_mkConst(v___x_1909_, v___x_1908_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* v_e_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
if (lean_obj_tag(v_e_1911_) == 7)
{
lean_object* v_binderName_1923_; lean_object* v_binderType_1924_; lean_object* v_body_1925_; uint8_t v_binderInfo_1926_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; uint8_t v___x_2135_; 
v_binderName_1923_ = lean_ctor_get(v_e_1911_, 0);
lean_inc(v_binderName_1923_);
v_binderType_1924_ = lean_ctor_get(v_e_1911_, 1);
lean_inc_ref(v_binderType_1924_);
v_body_1925_ = lean_ctor_get(v_e_1911_, 2);
lean_inc_ref(v_body_1925_);
v_binderInfo_1926_ = lean_ctor_get_uint8(v_e_1911_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1911_, 3);
v___x_2135_ = l_Lean_Expr_hasLooseBVars(v_body_1925_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; lean_object* v___y_2138_; lean_object* v___x_2162_; 
v___x_2136_ = 1;
lean_inc_ref(v_binderType_1924_);
v___x_2162_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1924_, v_a_1916_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = l_Lean_Expr_cleanupAnnotations(v_a_2163_);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2166_ = l_Lean_Expr_isConstOf(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2168_ = l_Lean_Expr_isConstOf(v___x_2164_, v___x_2167_);
lean_dec_ref(v___x_2164_);
if (v___x_2168_ == 0)
{
if (lean_obj_tag(v_binderType_1924_) == 7)
{
lean_object* v_binderName_2169_; lean_object* v_binderType_2170_; lean_object* v_body_2171_; uint8_t v_binderInfo_2172_; uint8_t v_a_2174_; uint8_t v___x_2207_; 
v_binderName_2169_ = lean_ctor_get(v_binderType_1924_, 0);
v_binderType_2170_ = lean_ctor_get(v_binderType_1924_, 1);
v_body_2171_ = lean_ctor_get(v_binderType_1924_, 2);
v_binderInfo_2172_ = lean_ctor_get_uint8(v_binderType_1924_, sizeof(void*)*3 + 8);
v___x_2207_ = l_Lean_Expr_hasLooseBVars(v_body_2171_);
if (v___x_2207_ == 0)
{
v_a_2174_ = v___x_2207_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2208_; 
lean_inc_ref(v_binderType_1924_);
v___x_2208_ = l_Lean_Meta_isProp(v_binderType_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; uint8_t v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
v_a_2174_ = v___x_2210_;
goto v___jp_2173_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref_known(v_binderType_1924_, 3);
lean_dec_ref(v_body_1925_);
lean_dec(v_binderName_1923_);
v_a_2211_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2208_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2208_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
v___jp_2173_:
{
if (v_a_2174_ == 0)
{
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_inc_ref_n(v_body_2171_, 2);
lean_inc_ref_n(v_binderType_2170_, 3);
lean_inc_n(v_binderName_2169_, 2);
lean_dec_ref_known(v_binderType_1924_, 3);
lean_dec(v_binderName_1923_);
v___x_2175_ = l_Lean_mkLambda(v_binderName_2169_, v_binderInfo_2172_, v_binderType_2170_, v_body_2171_);
v___x_2176_ = l_Lean_Meta_getLevel(v_binderType_2170_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2198_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2198_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2198_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_a_2177_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
lean_inc_ref(v___x_2183_);
v___x_2184_ = l_Lean_mkConst(v___x_2181_, v___x_2183_);
v___x_2185_ = l_Lean_mkNot(v_body_2171_);
lean_inc_ref_n(v_binderType_2170_, 2);
v___x_2186_ = l_Lean_mkLambda(v_binderName_2169_, v_binderInfo_2172_, v_binderType_2170_, v___x_2185_);
v___x_2187_ = l_Lean_mkAppB(v___x_2184_, v_binderType_2170_, v___x_2186_);
lean_inc_ref(v_body_1925_);
v___x_2188_ = l_Lean_mkOr(v___x_2187_, v_body_1925_);
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__18));
v___x_2190_ = l_Lean_mkConst(v___x_2189_, v___x_2183_);
v___x_2191_ = l_Lean_mkApp3(v___x_2190_, v_binderType_2170_, v___x_2175_, v_body_1925_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2193_, 0, v___x_2188_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_ctor_set_uint8(v___x_2193_, sizeof(void*)*2, v___x_2136_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2194_);
v___x_2196_ = v___x_2179_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v___x_2175_);
lean_dec_ref(v_body_2171_);
lean_dec_ref(v_binderType_2170_);
lean_dec(v_binderName_2169_);
lean_dec_ref(v_body_1925_);
v_a_2199_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2176_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2176_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
else
{
lean_object* v___x_2219_; 
lean_inc_ref(v_body_1925_);
v___x_2219_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_1925_, v_a_1916_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l_Lean_Expr_cleanupAnnotations(v_a_2220_);
v___x_2222_ = l_Lean_Expr_isConstOf(v___x_2221_, v___x_2165_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; 
v___x_2223_ = l_Lean_Expr_isConstOf(v___x_2221_, v___x_2167_);
lean_dec_ref(v___x_2221_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_inc_ref(v_binderType_1924_);
v___x_2224_ = l_Lean_Meta_isProp(v_binderType_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; uint8_t v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
v___x_2226_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
if (v___x_2226_ == 0)
{
v___y_2138_ = v___x_2224_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2227_; 
lean_dec_ref_known(v___x_2224_, 1);
lean_inc_ref(v_body_1925_);
lean_inc_ref(v_binderType_1924_);
v___x_2227_ = l_Lean_Meta_isExprDefEq(v_binderType_1924_, v_body_1925_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
v___y_2138_ = v___x_2227_;
goto v___jp_2137_;
}
}
else
{
v___y_2138_ = v___x_2224_;
goto v___jp_2137_;
}
}
else
{
lean_object* v___x_2228_; 
lean_inc_ref(v_binderType_1924_);
v___x_2228_ = l_Lean_Meta_isProp(v_binderType_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2243_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2243_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2243_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_unbox(v_a_2229_);
lean_dec(v_a_2229_);
if (v___x_2233_ == 0)
{
lean_del_object(v___x_2231_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec_ref(v_body_1925_);
lean_dec(v_binderName_1923_);
v___x_2234_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2235_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__21, &l_Lean_Meta_Grind_simpForall___closed__21_once, _init_l_Lean_Meta_Grind_simpForall___closed__21);
v___x_2236_ = l_Lean_Expr_app___override(v___x_2235_, v_binderType_1924_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2234_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*2, v___x_2136_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2239_);
v___x_2241_ = v___x_2231_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2244_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2228_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2228_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v___x_2252_; 
lean_dec_ref(v___x_2221_);
lean_inc_ref(v_binderType_1924_);
v___x_2252_ = l_Lean_Meta_isProp(v_binderType_1924_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2267_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2267_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2267_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
if (v___x_2257_ == 0)
{
lean_del_object(v___x_2255_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_dec_ref(v_body_1925_);
lean_dec(v_binderName_1923_);
lean_inc_ref(v_binderType_1924_);
v___x_2258_ = l_Lean_mkNot(v_binderType_1924_);
v___x_2259_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__24, &l_Lean_Meta_Grind_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_simpForall___closed__24);
v___x_2260_ = l_Lean_Expr_app___override(v___x_2259_, v_binderType_1924_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2262_, 0, v___x_2258_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*2, v___x_2136_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2263_);
v___x_2265_ = v___x_2255_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2268_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2252_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2252_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2276_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2219_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2219_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2284_; 
lean_inc_ref(v_body_1925_);
v___x_2284_ = l_Lean_Meta_isProp(v_body_1925_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2298_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2298_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_unbox(v_a_2285_);
lean_dec(v_a_2285_);
if (v___x_2289_ == 0)
{
lean_del_object(v___x_2287_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v___x_2290_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__27, &l_Lean_Meta_Grind_simpForall___closed__27_once, _init_l_Lean_Meta_Grind_simpForall___closed__27);
lean_inc_ref(v_body_1925_);
v___x_2291_ = l_Lean_Expr_app___override(v___x_2290_, v_body_1925_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2293_, 0, v_body_1925_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*2, v___x_2136_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2294_);
v___x_2296_ = v___x_2287_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2299_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2284_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2284_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v___x_2307_; 
lean_dec_ref(v___x_2164_);
lean_inc_ref(v_body_1925_);
v___x_2307_ = l_Lean_Meta_isProp(v_body_1925_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2322_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2322_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2322_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_unbox(v_a_2308_);
lean_dec(v_a_2308_);
if (v___x_2312_ == 0)
{
lean_del_object(v___x_2310_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2314_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
v___x_2315_ = l_Lean_Expr_app___override(v___x_2314_, v_body_1925_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2317_, 0, v___x_2313_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
lean_ctor_set_uint8(v___x_2317_, sizeof(void*)*2, v___x_2136_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2318_);
v___x_2320_ = v___x_2310_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2323_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2307_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2307_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2331_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2162_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2162_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
v___jp_2137_:
{
if (lean_obj_tag(v___y_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2153_; 
v_a_2139_ = lean_ctor_get(v___y_2138_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___y_2138_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2141_ = v___y_2138_;
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___y_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_unbox(v_a_2139_);
lean_dec(v_a_2139_);
if (v___x_2143_ == 0)
{
lean_del_object(v___x_2141_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
lean_dec_ref(v_body_1925_);
lean_dec(v_binderName_1923_);
v___x_2144_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2145_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__16, &l_Lean_Meta_Grind_simpForall___closed__16_once, _init_l_Lean_Meta_Grind_simpForall___closed__16);
v___x_2146_ = l_Lean_Expr_app___override(v___x_2145_, v_binderType_1924_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2144_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2, v___x_2136_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2149_);
v___x_2151_ = v___x_2141_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2154_ = lean_ctor_get(v___y_2138_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___y_2138_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___y_2138_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___y_2138_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
else
{
lean_object* v___x_2339_; 
lean_inc_ref(v_binderType_1924_);
v___x_2339_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1924_, v_a_1916_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_Expr_cleanupAnnotations(v_a_2340_);
v___x_2342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2343_ = l_Lean_Expr_isConstOf(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__12));
v___x_2345_ = l_Lean_Expr_isConstOf(v___x_2341_, v___x_2344_);
lean_dec_ref(v___x_2341_);
if (v___x_2345_ == 0)
{
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__33, &l_Lean_Meta_Grind_simpForall___closed__33_once, _init_l_Lean_Meta_Grind_simpForall___closed__33);
v___x_2347_ = lean_expr_instantiate1(v_body_1925_, v___x_2346_);
lean_inc_ref(v___x_2347_);
v___x_2348_ = l_Lean_Meta_isProp(v___x_2347_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2363_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2363_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_unbox(v_a_2349_);
lean_dec(v_a_2349_);
if (v___x_2353_ == 0)
{
lean_del_object(v___x_2351_);
lean_dec_ref(v___x_2347_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2354_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_body_1925_);
v___x_2355_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__36, &l_Lean_Meta_Grind_simpForall___closed__36_once, _init_l_Lean_Meta_Grind_simpForall___closed__36);
v___x_2356_ = l_Lean_Expr_app___override(v___x_2355_, v___x_2354_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2358_, 0, v___x_2347_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*2, v___x_2135_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2359_);
v___x_2361_ = v___x_2351_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___x_2347_);
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2364_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2348_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2348_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec_ref(v___x_2341_);
lean_inc_ref(v_body_1925_);
lean_inc_ref(v_binderType_1924_);
lean_inc(v_binderName_1923_);
v___x_2372_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_body_1925_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
lean_inc(v_a_1916_);
lean_inc_ref(v_a_1915_);
lean_inc_ref(v___x_2372_);
v___x_2373_ = lean_infer_type(v___x_2372_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__38, &l_Lean_Meta_Grind_simpForall___closed__38_once, _init_l_Lean_Meta_Grind_simpForall___closed__38);
lean_inc_ref(v_binderType_1924_);
lean_inc(v_binderName_1923_);
v___x_2376_ = l_Lean_mkForall(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v___x_2375_);
v___x_2377_ = l_Lean_Meta_isExprDefEq(v_a_2374_, v___x_2376_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2392_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2380_ = v___x_2377_;
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2377_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2392_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint8_t v___x_2382_; 
v___x_2382_ = lean_unbox(v_a_2378_);
lean_dec(v_a_2378_);
if (v___x_2382_ == 0)
{
lean_del_object(v___x_2380_);
lean_dec_ref(v___x_2372_);
v___y_2124_ = v_a_1912_;
v___y_2125_ = v_a_1913_;
v___y_2126_ = v_a_1914_;
v___y_2127_ = v_a_1915_;
v___y_2128_ = v_a_1916_;
v___y_2129_ = v_a_1917_;
v___y_2130_ = v_a_1918_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__13, &l_Lean_Meta_Grind_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_simpForall___closed__13);
v___x_2384_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__41, &l_Lean_Meta_Grind_simpForall___closed__41_once, _init_l_Lean_Meta_Grind_simpForall___closed__41);
v___x_2385_ = l_Lean_Expr_app___override(v___x_2384_, v___x_2372_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2387_, 0, v___x_2383_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*2, v___x_2135_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2388_);
v___x_2390_ = v___x_2380_;
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
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v___x_2372_);
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2393_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2377_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2377_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v___x_2372_);
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2401_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2373_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2373_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2409_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2339_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2339_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
v___jp_1927_:
{
if (v___y_1935_ == 0)
{
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
goto v___jp_1920_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = l_Lean_Expr_appFn_x21(v_body_1925_);
v___x_1937_ = l_Lean_Expr_appFn_x21(v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 4)
{
lean_object* v_declName_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_declName_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_declName_1938_);
lean_dec_ref_known(v___x_1937_, 2);
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_1940_ = lean_name_eq(v_declName_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_1942_ = lean_name_eq(v_declName_1938_, v___x_1941_);
lean_dec(v_declName_1938_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v___x_1936_);
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
goto v___jp_1920_;
}
else
{
lean_object* v_pRaw_1943_; lean_object* v_qRaw_1944_; lean_object* v_p_1945_; lean_object* v_q_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_expr_1949_; lean_object* v___x_1950_; 
v_pRaw_1943_ = l_Lean_Expr_appArg_x21(v___x_1936_);
lean_dec_ref(v___x_1936_);
v_qRaw_1944_ = l_Lean_Expr_appArg_x21(v_body_1925_);
lean_dec_ref(v_body_1925_);
lean_inc_ref(v_pRaw_1943_);
lean_inc_ref_n(v_binderType_1924_, 5);
lean_inc_n(v_binderName_1923_, 3);
v_p_1945_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_pRaw_1943_);
lean_inc_ref(v_qRaw_1944_);
v_q_1946_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_qRaw_1944_);
v___x_1947_ = l_Lean_mkForall(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_pRaw_1943_);
v___x_1948_ = l_Lean_mkForall(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_qRaw_1944_);
v_expr_1949_ = l_Lean_mkAnd(v___x_1947_, v___x_1948_);
v___x_1950_ = l_Lean_Meta_getLevel(v_binderType_1924_, v___y_1931_, v___y_1932_, v___y_1934_, v___y_1930_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1966_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1966_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1966_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1955_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1951_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_mkConst(v___x_1955_, v___x_1957_);
v___x_1959_ = l_Lean_mkApp3(v___x_1958_, v_binderType_1924_, v_p_1945_, v_q_1946_);
v___x_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1961_, 0, v_expr_1949_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*2, v___y_1935_);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1962_);
v___x_1964_ = v___x_1953_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_expr_1949_);
lean_dec_ref(v_q_1946_);
lean_dec_ref(v_p_1945_);
lean_dec_ref(v_binderType_1924_);
v_a_1967_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1950_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1950_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_pRaw_1975_; lean_object* v_pRaw_1976_; lean_object* v___x_1977_; 
lean_dec(v_declName_1938_);
v_pRaw_1975_ = l_Lean_Expr_appArg_x21(v___x_1936_);
lean_dec_ref(v___x_1936_);
v_pRaw_1976_ = l_Lean_Expr_appArg_x21(v_body_1925_);
lean_dec_ref(v_body_1925_);
v___x_1977_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1975_);
if (lean_obj_tag(v___x_1977_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_pRaw_1975_);
v_val_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2048_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_val_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2048_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_snd_1982_; lean_object* v_fst_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2047_; 
v_snd_1982_ = lean_ctor_get(v_val_1978_, 1);
v_fst_1983_ = lean_ctor_get(v_val_1978_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_val_1978_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_1985_ = v_val_1978_;
v_isShared_1986_ = v_isSharedCheck_2047_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1983_);
lean_dec(v_val_1978_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2047_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2046_; 
v_fst_1987_ = lean_ctor_get(v_snd_1982_, 0);
v_snd_1988_ = lean_ctor_get(v_snd_1982_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_snd_1982_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_1990_ = v_snd_1982_;
v_isShared_1991_ = v_isSharedCheck_2046_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snd_1988_);
lean_inc(v_fst_1987_);
lean_dec(v_snd_1982_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2046_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___f_1992_; lean_object* v_p_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v_q_1996_; lean_object* v_00_u03b2_1997_; lean_object* v___x_1998_; 
lean_inc_n(v_fst_1987_, 3);
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1992_, 0, v_fst_1987_);
lean_inc_ref(v_pRaw_1976_);
lean_inc_ref_n(v_binderType_1924_, 4);
lean_inc_n(v_binderName_1923_, 3);
v_p_1993_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_pRaw_1976_);
v___x_1994_ = 0;
lean_inc(v_snd_1988_);
lean_inc(v_fst_1983_);
v___x_1995_ = l_Lean_mkLambda(v_fst_1983_, v___x_1994_, v_fst_1987_, v_snd_1988_);
v_q_1996_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v___x_1995_);
v_00_u03b2_1997_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_fst_1987_);
v___x_1998_ = l_Lean_Meta_getLevel(v_binderType_1924_, v___y_1931_, v___y_1932_, v___y_1934_, v___y_1930_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
lean_inc_ref(v_binderType_1924_);
lean_inc(v_binderName_1923_);
v___x_2000_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1923_, v_binderType_1924_, v___f_1992_, v___y_1929_, v___y_1933_, v___y_1928_, v___y_1931_, v___y_1932_, v___y_1934_, v___y_1930_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2029_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2029_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2029_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_expr_lift_loose_bvars(v_pRaw_1976_, v___x_2005_, v___x_2006_);
lean_dec_ref(v_pRaw_1976_);
v___x_2008_ = l_Lean_mkOr(v_snd_1988_, v___x_2007_);
v___x_2009_ = l_Lean_mkForall(v_fst_1983_, v___x_1994_, v_fst_1987_, v___x_2008_);
lean_inc_ref(v_binderType_1924_);
v___x_2010_ = l_Lean_mkForall(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v___x_2009_);
v___x_2011_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2012_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 1);
lean_ctor_set(v___x_1990_, 1, v___x_2012_);
lean_ctor_set(v___x_1990_, 0, v_a_2001_);
v___x_2014_ = v___x_1990_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2001_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 1, v___x_2014_);
lean_ctor_set(v___x_1985_, 0, v_a_1999_);
v___x_2016_ = v___x_1985_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_1999_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2017_ = l_Lean_mkConst(v___x_2011_, v___x_2016_);
v___x_2018_ = l_Lean_mkApp4(v___x_2017_, v_binderType_1924_, v_00_u03b2_1997_, v_p_1993_, v_q_1996_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2018_);
v___x_2020_ = v___x_1980_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2021_, 0, v___x_2010_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*2, v___y_1935_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2022_);
v___x_2024_ = v___x_2003_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_1999_);
lean_dec_ref(v_00_u03b2_1997_);
lean_dec_ref(v_q_1996_);
lean_dec_ref(v_p_1993_);
lean_del_object(v___x_1990_);
lean_dec(v_snd_1988_);
lean_dec(v_fst_1987_);
lean_del_object(v___x_1985_);
lean_dec(v_fst_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v_pRaw_1976_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2030_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2000_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2000_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_00_u03b2_1997_);
lean_dec_ref(v_q_1996_);
lean_dec_ref(v_p_1993_);
lean_dec_ref(v___f_1992_);
lean_del_object(v___x_1990_);
lean_dec(v_snd_1988_);
lean_dec(v_fst_1987_);
lean_del_object(v___x_1985_);
lean_dec(v_fst_1983_);
lean_del_object(v___x_1980_);
lean_dec_ref(v_pRaw_1976_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2038_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1998_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1998_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2049_; 
lean_dec(v___x_1977_);
v___x_2049_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1976_);
lean_dec_ref(v_pRaw_1976_);
if (lean_obj_tag(v___x_2049_) == 1)
{
lean_object* v_val_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2120_; 
v_val_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2120_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_val_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2120_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_snd_2054_; lean_object* v_fst_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2119_; 
v_snd_2054_ = lean_ctor_get(v_val_2050_, 1);
v_fst_2055_ = lean_ctor_get(v_val_2050_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_val_2050_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2057_ = v_val_2050_;
v_isShared_2058_ = v_isSharedCheck_2119_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2055_);
lean_dec(v_val_2050_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2119_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2118_; 
v_fst_2059_ = lean_ctor_get(v_snd_2054_, 0);
v_snd_2060_ = lean_ctor_get(v_snd_2054_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_snd_2054_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2062_ = v_snd_2054_;
v_isShared_2063_ = v_isSharedCheck_2118_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snd_2060_);
lean_inc(v_fst_2059_);
lean_dec(v_snd_2054_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2118_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___f_2064_; lean_object* v_p_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v_q_2068_; lean_object* v_00_u03b2_2069_; lean_object* v___x_2070_; 
lean_inc_n(v_fst_2059_, 3);
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2064_, 0, v_fst_2059_);
lean_inc_ref(v_pRaw_1975_);
lean_inc_ref_n(v_binderType_1924_, 4);
lean_inc_n(v_binderName_1923_, 3);
v_p_2065_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_pRaw_1975_);
v___x_2066_ = 0;
lean_inc(v_snd_2060_);
lean_inc(v_fst_2055_);
v___x_2067_ = l_Lean_mkLambda(v_fst_2055_, v___x_2066_, v_fst_2059_, v_snd_2060_);
v_q_2068_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v___x_2067_);
v_00_u03b2_2069_ = l_Lean_mkLambda(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v_fst_2059_);
v___x_2070_ = l_Lean_Meta_getLevel(v_binderType_1924_, v___y_1931_, v___y_1932_, v___y_1934_, v___y_1930_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
lean_inc_ref(v_binderType_1924_);
lean_inc(v_binderName_1923_);
v___x_2072_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1923_, v_binderType_1924_, v___f_2064_, v___y_1929_, v___y_1933_, v___y_1928_, v___y_1931_, v___y_1932_, v___y_1934_, v___y_1930_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2101_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2101_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2101_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_unsigned_to_nat(1u);
v___x_2079_ = lean_expr_lift_loose_bvars(v_pRaw_1975_, v___x_2077_, v___x_2078_);
lean_dec_ref(v_pRaw_1975_);
v___x_2080_ = l_Lean_mkOr(v___x_2079_, v_snd_2060_);
v___x_2081_ = l_Lean_mkForall(v_fst_2055_, v___x_2066_, v_fst_2059_, v___x_2080_);
lean_inc_ref(v_binderType_1924_);
v___x_2082_ = l_Lean_mkForall(v_binderName_1923_, v_binderInfo_1926_, v_binderType_1924_, v___x_2081_);
v___x_2083_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__10));
v___x_2084_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
lean_ctor_set(v___x_2062_, 1, v___x_2084_);
lean_ctor_set(v___x_2062_, 0, v_a_2073_);
v___x_2086_ = v___x_2062_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2073_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 1, v___x_2086_);
lean_ctor_set(v___x_2057_, 0, v_a_2071_);
v___x_2088_ = v___x_2057_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2071_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2089_ = l_Lean_mkConst(v___x_2083_, v___x_2088_);
v___x_2090_ = l_Lean_mkApp4(v___x_2089_, v_binderType_1924_, v_00_u03b2_2069_, v_p_2065_, v_q_2068_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2090_);
v___x_2092_ = v___x_2052_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2093_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2082_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2, v___y_1935_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2094_);
v___x_2096_ = v___x_2075_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2071_);
lean_dec_ref(v_00_u03b2_2069_);
lean_dec_ref(v_q_2068_);
lean_dec_ref(v_p_2065_);
lean_del_object(v___x_2062_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2059_);
lean_del_object(v___x_2057_);
lean_dec(v_fst_2055_);
lean_del_object(v___x_2052_);
lean_dec_ref(v_pRaw_1975_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2102_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2072_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2072_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_00_u03b2_2069_);
lean_dec_ref(v_q_2068_);
lean_dec_ref(v_p_2065_);
lean_dec_ref(v___f_2064_);
lean_del_object(v___x_2062_);
lean_dec(v_snd_2060_);
lean_dec(v_fst_2059_);
lean_del_object(v___x_2057_);
lean_dec(v_fst_2055_);
lean_del_object(v___x_2052_);
lean_dec_ref(v_pRaw_1975_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v_a_2110_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2070_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2070_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2049_);
lean_dec_ref(v_pRaw_1975_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
goto v___jp_1920_;
}
}
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref(v___x_1937_);
lean_dec_ref(v___x_1936_);
lean_dec_ref(v_body_1925_);
lean_dec_ref(v_binderType_1924_);
lean_dec(v_binderName_1923_);
v___x_2121_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
}
v___jp_2123_:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Lean_Expr_isApp(v_body_1925_);
if (v___x_2131_ == 0)
{
v___y_1928_ = v___y_2126_;
v___y_1929_ = v___y_2124_;
v___y_1930_ = v___y_2130_;
v___y_1931_ = v___y_2127_;
v___y_1932_ = v___y_2128_;
v___y_1933_ = v___y_2125_;
v___y_1934_ = v___y_2129_;
v___y_1935_ = v___x_2131_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = l_Lean_Expr_getAppNumArgs(v_body_1925_);
v___x_2133_ = lean_unsigned_to_nat(2u);
v___x_2134_ = lean_nat_dec_eq(v___x_2132_, v___x_2133_);
lean_dec(v___x_2132_);
v___y_1928_ = v___y_2126_;
v___y_1929_ = v___y_2124_;
v___y_1930_ = v___y_2130_;
v___y_1931_ = v___y_2127_;
v___y_1932_ = v___y_2128_;
v___y_1933_ = v___y_2125_;
v___y_1934_ = v___y_2129_;
v___y_1935_ = v___x_2134_;
goto v___jp_1927_;
}
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v_e_1911_);
v___x_2417_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
v___jp_1920_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* v_e_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Meta_Grind_simpForall(v_e_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* v_00_u03b1_2429_, lean_object* v_name_2430_, uint8_t v_bi_2431_, lean_object* v_type_2432_, lean_object* v_k_2433_, uint8_t v_kind_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_2430_, v_bi_2431_, v_type_2432_, v_k_2433_, v_kind_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_name_2445_, lean_object* v_bi_2446_, lean_object* v_type_2447_, lean_object* v_k_2448_, lean_object* v_kind_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
uint8_t v_bi_boxed_2458_; uint8_t v_kind_boxed_2459_; lean_object* v_res_2460_; 
v_bi_boxed_2458_ = lean_unbox(v_bi_2446_);
v_kind_boxed_2459_ = lean_unbox(v_kind_2449_);
v_res_2460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_2444_, v_name_2445_, v_bi_boxed_2458_, v_type_2447_, v_k_2448_, v_kind_boxed_2459_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* v_00_u03b1_2461_, lean_object* v_name_2462_, lean_object* v_type_2463_, lean_object* v_k_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_2462_, v_type_2463_, v_k_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* v_00_u03b1_2474_, lean_object* v_name_2475_, lean_object* v_type_2476_, lean_object* v_k_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(v_00_u03b1_2474_, v_name_2475_, v_type_2476_, v_k_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2503_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
v___x_2504_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2501_, v___x_2502_, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12____boxed(lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_();
return v_res_2506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_box(0);
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
v___x_2522_ = l_Lean_mkConst(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* v_e_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = l_Lean_Expr_cleanupAnnotations(v_e_2538_);
v___x_2551_ = l_Lean_Expr_isApp(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_dec_ref(v___x_2550_);
goto v___jp_2544_;
}
else
{
lean_object* v_arg_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_arg_2552_ = lean_ctor_get(v___x_2550_, 1);
lean_inc_ref(v_arg_2552_);
v___x_2553_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2550_);
v___x_2554_ = l_Lean_Expr_isApp(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_dec_ref(v___x_2553_);
lean_dec_ref(v_arg_2552_);
goto v___jp_2544_;
}
else
{
lean_object* v_arg_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_arg_2555_ = lean_ctor_get(v___x_2553_, 1);
lean_inc_ref(v_arg_2555_);
v___x_2556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2553_);
v___x_2557_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2558_ = l_Lean_Expr_isConstOf(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
lean_dec_ref(v_arg_2552_);
goto v___jp_2544_;
}
else
{
if (lean_obj_tag(v_arg_2552_) == 6)
{
lean_object* v_binderName_2559_; lean_object* v_body_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; uint8_t v___y_2629_; uint8_t v___y_2656_; uint8_t v___x_2685_; 
v_binderName_2559_ = lean_ctor_get(v_arg_2552_, 0);
lean_inc(v_binderName_2559_);
v_body_2560_ = lean_ctor_get(v_arg_2552_, 2);
lean_inc_ref(v_body_2560_);
lean_dec_ref_known(v_arg_2552_, 3);
v___x_2685_ = l_Lean_Expr_isApp(v_body_2560_);
if (v___x_2685_ == 0)
{
v___y_2656_ = v___x_2685_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = l_Lean_Expr_getAppNumArgs(v_body_2560_);
v___x_2687_ = lean_unsigned_to_nat(2u);
v___x_2688_ = lean_nat_dec_eq(v___x_2686_, v___x_2687_);
lean_dec(v___x_2686_);
v___y_2656_ = v___x_2688_;
goto v___jp_2655_;
}
v___jp_2561_:
{
uint8_t v___x_2566_; 
v___x_2566_ = l_Lean_Expr_hasLooseBVars(v_body_2560_);
if (v___x_2566_ == 0)
{
if (v___x_2558_ == 0)
{
lean_dec_ref(v_body_2560_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
goto v___jp_2547_;
}
else
{
lean_object* v___x_2567_; 
lean_inc_ref(v_arg_2555_);
v___x_2567_ = l_Lean_Meta_isProp(v_arg_2555_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2616_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2616_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2616_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_unbox(v_a_2568_);
lean_dec(v_a_2568_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_del_object(v___x_2570_);
v___x_2573_ = l_Lean_Expr_constLevels_x21(v___x_2556_);
lean_dec_ref(v___x_2556_);
v___x_2574_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(v___x_2573_);
v___x_2575_ = l_Lean_mkConst(v___x_2574_, v___x_2573_);
lean_inc_ref(v_arg_2555_);
v___x_2576_ = l_Lean_Expr_app___override(v___x_2575_, v_arg_2555_);
v___x_2577_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2576_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2598_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2598_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2598_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
if (lean_obj_tag(v_a_2578_) == 1)
{
lean_object* v_val_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2597_; 
v_val_2582_ = lean_ctor_get(v_a_2578_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2584_ = v_a_2578_;
v_isShared_2585_ = v_isSharedCheck_2597_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_val_2582_);
lean_dec(v_a_2578_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2597_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2586_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
v___x_2587_ = l_Lean_mkConst(v___x_2586_, v___x_2573_);
lean_inc_ref(v_body_2560_);
v___x_2588_ = l_Lean_mkApp3(v___x_2587_, v_arg_2555_, v_val_2582_, v_body_2560_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2588_);
v___x_2590_ = v___x_2584_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2591_, 0, v_body_2560_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*2, v___x_2558_);
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2592_);
v___x_2594_ = v___x_2580_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_del_object(v___x_2580_);
lean_dec(v_a_2578_);
lean_dec(v___x_2573_);
lean_dec_ref(v_body_2560_);
lean_dec_ref(v_arg_2555_);
goto v___jp_2547_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v___x_2573_);
lean_dec_ref(v_body_2560_);
lean_dec_ref(v_arg_2555_);
v_a_2599_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2577_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2577_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec_ref(v___x_2556_);
lean_inc_ref(v_body_2560_);
lean_inc_ref(v_arg_2555_);
v___x_2607_ = l_Lean_mkAnd(v_arg_2555_, v_body_2560_);
v___x_2608_ = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
v___x_2609_ = l_Lean_mkAppB(v___x_2608_, v_arg_2555_, v_body_2560_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2607_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*2, v___x_2558_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2612_);
v___x_2614_ = v___x_2570_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_body_2560_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
v_a_2617_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2567_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2567_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_dec_ref(v_body_2560_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
goto v___jp_2547_;
}
}
v___jp_2625_:
{
if (v___y_2629_ == 0)
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_Expr_hasLooseBVars(v___y_2627_);
if (v___x_2630_ == 0)
{
if (v___y_2626_ == 0)
{
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v_binderName_2559_);
v___y_2562_ = v_a_2539_;
v___y_2563_ = v_a_2540_;
v___y_2564_ = v_a_2541_;
v___y_2565_ = v_a_2542_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2631_; lean_object* v_p_2632_; lean_object* v___x_2633_; lean_object* v_expr_2634_; lean_object* v_u_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref(v_body_2560_);
v___x_2631_ = 0;
lean_inc_ref_n(v_arg_2555_, 2);
v_p_2632_ = l_Lean_mkLambda(v_binderName_2559_, v___x_2631_, v_arg_2555_, v___y_2628_);
lean_inc_ref(v_p_2632_);
lean_inc_ref(v___x_2556_);
v___x_2633_ = l_Lean_mkAppB(v___x_2556_, v_arg_2555_, v_p_2632_);
lean_inc_ref(v___y_2627_);
v_expr_2634_ = l_Lean_mkAnd(v___x_2633_, v___y_2627_);
v_u_2635_ = l_Lean_Expr_constLevels_x21(v___x_2556_);
lean_dec_ref(v___x_2556_);
v___x_2636_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
v___x_2637_ = l_Lean_mkConst(v___x_2636_, v_u_2635_);
v___x_2638_ = l_Lean_mkApp3(v___x_2637_, v_arg_2555_, v_p_2632_, v___y_2627_);
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2640_, 0, v_expr_2634_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*2, v___x_2558_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
else
{
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v_binderName_2559_);
v___y_2562_ = v_a_2539_;
v___y_2563_ = v_a_2540_;
v___y_2564_ = v_a_2541_;
v___y_2565_ = v_a_2542_;
goto v___jp_2561_;
}
}
else
{
uint8_t v___x_2643_; lean_object* v_p_2644_; lean_object* v___x_2645_; lean_object* v_expr_2646_; lean_object* v_u_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref(v_body_2560_);
v___x_2643_ = 0;
lean_inc_ref_n(v_arg_2555_, 2);
v_p_2644_ = l_Lean_mkLambda(v_binderName_2559_, v___x_2643_, v_arg_2555_, v___y_2627_);
lean_inc_ref(v_p_2644_);
lean_inc_ref(v___x_2556_);
v___x_2645_ = l_Lean_mkAppB(v___x_2556_, v_arg_2555_, v_p_2644_);
lean_inc_ref(v___y_2628_);
v_expr_2646_ = l_Lean_mkAnd(v___y_2628_, v___x_2645_);
v_u_2647_ = l_Lean_Expr_constLevels_x21(v___x_2556_);
lean_dec_ref(v___x_2556_);
v___x_2648_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
v___x_2649_ = l_Lean_mkConst(v___x_2648_, v_u_2647_);
v___x_2650_ = l_Lean_mkApp3(v___x_2649_, v_arg_2555_, v_p_2644_, v___y_2628_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2652_, 0, v_expr_2646_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
lean_ctor_set_uint8(v___x_2652_, sizeof(void*)*2, v___x_2558_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
v___jp_2655_:
{
if (v___y_2656_ == 0)
{
lean_dec(v_binderName_2559_);
v___y_2562_ = v_a_2539_;
v___y_2563_ = v_a_2540_;
v___y_2564_ = v_a_2541_;
v___y_2565_ = v_a_2542_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = l_Lean_Expr_appFn_x21(v_body_2560_);
v___x_2658_ = l_Lean_Expr_appFn_x21(v___x_2657_);
if (lean_obj_tag(v___x_2658_) == 4)
{
lean_object* v_declName_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v_declName_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_declName_2659_);
lean_dec_ref_known(v___x_2658_, 2);
v___x_2660_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_2661_ = lean_name_eq(v_declName_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_2663_ = lean_name_eq(v_declName_2659_, v___x_2662_);
lean_dec(v_declName_2659_);
if (v___x_2663_ == 0)
{
lean_dec_ref(v___x_2657_);
lean_dec(v_binderName_2559_);
v___y_2562_ = v_a_2539_;
v___y_2563_ = v_a_2540_;
v___y_2564_ = v_a_2541_;
v___y_2565_ = v_a_2542_;
goto v___jp_2561_;
}
else
{
lean_object* v_b_2664_; lean_object* v_b_2665_; uint8_t v___x_2666_; 
v_b_2664_ = l_Lean_Expr_appArg_x21(v___x_2657_);
lean_dec_ref(v___x_2657_);
v_b_2665_ = l_Lean_Expr_appArg_x21(v_body_2560_);
v___x_2666_ = l_Lean_Expr_hasLooseBVars(v_b_2664_);
if (v___x_2666_ == 0)
{
v___y_2626_ = v___x_2663_;
v___y_2627_ = v_b_2665_;
v___y_2628_ = v_b_2664_;
v___y_2629_ = v___x_2663_;
goto v___jp_2625_;
}
else
{
v___y_2626_ = v___x_2663_;
v___y_2627_ = v_b_2665_;
v___y_2628_ = v_b_2664_;
v___y_2629_ = v___x_2661_;
goto v___jp_2625_;
}
}
}
else
{
lean_object* v_pRaw_2667_; lean_object* v_qRaw_2668_; uint8_t v___x_2669_; lean_object* v_p_2670_; lean_object* v_q_2671_; lean_object* v_u_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_expr_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec(v_declName_2659_);
v_pRaw_2667_ = l_Lean_Expr_appArg_x21(v___x_2657_);
lean_dec_ref(v___x_2657_);
v_qRaw_2668_ = l_Lean_Expr_appArg_x21(v_body_2560_);
lean_dec_ref(v_body_2560_);
v___x_2669_ = 0;
lean_inc_ref_n(v_arg_2555_, 4);
lean_inc(v_binderName_2559_);
v_p_2670_ = l_Lean_mkLambda(v_binderName_2559_, v___x_2669_, v_arg_2555_, v_pRaw_2667_);
v_q_2671_ = l_Lean_mkLambda(v_binderName_2559_, v___x_2669_, v_arg_2555_, v_qRaw_2668_);
v_u_2672_ = l_Lean_Expr_constLevels_x21(v___x_2556_);
lean_inc_ref(v_p_2670_);
lean_inc_ref(v___x_2556_);
v___x_2673_ = l_Lean_mkAppB(v___x_2556_, v_arg_2555_, v_p_2670_);
lean_inc_ref(v_q_2671_);
v___x_2674_ = l_Lean_mkAppB(v___x_2556_, v_arg_2555_, v_q_2671_);
v_expr_2675_ = l_Lean_mkOr(v___x_2673_, v___x_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
v___x_2677_ = l_Lean_mkConst(v___x_2676_, v_u_2672_);
v___x_2678_ = l_Lean_mkApp3(v___x_2677_, v_arg_2555_, v_p_2670_, v_q_2671_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2680_, 0, v_expr_2675_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_ctor_set_uint8(v___x_2680_, sizeof(void*)*2, v___x_2558_);
v___x_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_dec_ref(v___x_2658_);
lean_dec_ref(v___x_2657_);
lean_dec_ref(v_body_2560_);
lean_dec(v_binderName_2559_);
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
v___x_2683_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec_ref(v___x_2556_);
lean_dec_ref(v_arg_2555_);
lean_dec_ref(v_arg_2552_);
v___x_2689_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
v___jp_2547_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* v_e_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* v_e_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2698_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* v_e_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_Grind_simpExists(v_e_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2737_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
v___x_2738_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2735_, v___x_2736_, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11____boxed(lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* v_s_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_));
v___x_2746_ = 1;
v___x_2747_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2741_, v___x_2745_, v___x_2746_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2750_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2748_, v___x_2749_, v___x_2746_, v_a_2742_, v_a_2743_);
return v___x_2750_;
}
else
{
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* v_s_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Meta_Grind_addForallSimproc(v_s_2751_, v_a_2752_, v_a_2753_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2755_;
}
}
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
}
#ifdef __cplusplus
}
#endif
