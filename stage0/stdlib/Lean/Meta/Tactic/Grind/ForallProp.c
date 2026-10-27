// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: public import Init.Grind.Propagator import Init.Simproc import Init.Grind.Norm import Lean.Meta.Tactic.Grind.ForallAnd import Lean.Meta.Tactic.Grind.Internalize import Lean.Meta.Tactic.Grind.Anchor import Lean.Meta.Tactic.Grind.EqResolution import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Grind.Lemmas
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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_forall_or"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 112, 166, 94, 237, 48, 167, 129)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_or_forall"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 14, 212, 131, 198, 226, 199, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__9;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_self_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__10_value),LEAN_SCALAR_PTR_LITERAL(166, 96, 8, 70, 216, 37, 74, 175)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__12;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "implies_true"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__13_value),LEAN_SCALAR_PTR_LITERAL(104, 135, 195, 91, 224, 240, 122, 198)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__15_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__17;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__18_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__20;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__21_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__23;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__24_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__26;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__27_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__29;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__31;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__32_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__34;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpForall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 161, 230, 164, 57, 132, 181, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12____boxed(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpExists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
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
uint8_t v_a_146_; lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_b_37_, v_a_38_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_229_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_229_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_229_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_229_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_a_183_);
lean_dec(v_a_183_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v___x_188_ = lean_box(0);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_192_; 
lean_del_object(v___x_185_);
lean_inc_ref(v_a_36_);
v___x_192_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_a_36_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; uint8_t v___x_194_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = lean_unbox(v_a_193_);
if (v___x_194_ == 0)
{
uint8_t v___x_195_; 
v___x_195_ = lean_unbox(v_a_193_);
lean_dec(v_a_193_);
v_a_146_ = v___x_195_;
goto v___jp_145_;
}
else
{
lean_object* v___x_196_; 
lean_dec(v_a_193_);
lean_inc_ref(v_b_37_);
v___x_196_ = l_Lean_Meta_isProp(v_b_37_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = lean_unbox(v_a_197_);
if (v___x_198_ == 0)
{
uint8_t v___x_199_; 
v___x_199_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
v_a_146_ = v___x_199_;
goto v___jp_145_;
}
else
{
lean_object* v___x_200_; 
lean_dec(v_a_197_);
lean_inc_ref(v_a_36_);
v___x_200_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_36_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
v___x_203_ = l_Lean_mkApp3(v___x_202_, v_a_36_, v_b_37_, v_a_201_);
v___x_204_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_35_, v___x_203_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_204_;
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_205_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_200_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_200_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_213_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_196_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_196_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_221_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_192_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_192_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_230_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_182_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_182_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
v___jp_49_:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
v___jp_52_:
{
lean_object* v___x_53_; 
lean_inc_ref(v_b_37_);
v___x_53_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_b_37_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; uint8_t v___x_55_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = lean_unbox(v_a_54_);
lean_dec(v_a_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
goto v___jp_49_;
}
else
{
lean_object* v___x_56_; 
lean_inc_ref(v_e_35_);
v___x_56_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_35_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; uint8_t v___x_58_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
lean_dec_ref_known(v___x_56_, 1);
v___x_58_ = lean_unbox(v_a_57_);
lean_dec(v_a_57_);
if (v___x_58_ == 0)
{
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
goto v___jp_49_;
}
else
{
lean_object* v___x_59_; 
lean_inc_ref(v_a_36_);
v___x_59_ = l_Lean_Meta_isProp(v_a_36_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; uint8_t v___x_61_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_59_, 1);
v___x_61_ = lean_unbox(v_a_60_);
lean_dec(v_a_60_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
goto v___jp_49_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_35_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_62_, 1);
lean_inc_ref(v_b_37_);
v___x_64_ = l_Lean_Meta_Grind_mkEqFalseProof(v_b_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v___x_64_, 1);
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_a_36_);
v___x_67_ = l_Lean_mkApp4(v___x_66_, v_a_36_, v_b_37_, v_a_63_, v_a_65_);
v___x_68_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_a_36_, v___x_67_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_68_;
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec(v_a_63_);
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
v_a_69_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_64_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
v_a_77_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_62_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_62_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_85_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_59_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_59_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_93_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_56_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_56_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_101_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_53_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_53_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
v___jp_109_:
{
lean_object* v___x_110_; 
lean_inc_ref(v_b_37_);
v___x_110_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_b_37_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; uint8_t v___x_112_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = lean_unbox(v_a_111_);
lean_dec(v_a_111_);
if (v___x_112_ == 0)
{
goto v___jp_52_;
}
else
{
lean_object* v___x_113_; 
lean_inc_ref(v_a_36_);
v___x_113_ = l_Lean_Meta_isProp(v_a_36_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; uint8_t v___x_115_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = lean_unbox(v_a_114_);
lean_dec(v_a_114_);
if (v___x_115_ == 0)
{
goto v___jp_52_;
}
else
{
lean_object* v___x_116_; 
lean_inc_ref(v_b_37_);
v___x_116_ = l_Lean_Meta_Grind_mkEqTrueProof(v_b_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
v___x_119_ = l_Lean_mkApp3(v___x_118_, v_a_36_, v_b_37_, v_a_117_);
v___x_120_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_35_, v___x_119_, v_a_38_, v_a_40_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_121_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_116_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_116_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_129_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_113_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_113_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_137_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_110_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_110_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
v___jp_145_:
{
lean_object* v___x_147_; 
lean_inc_ref(v_a_36_);
v___x_147_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_a_36_, v_a_38_, v_a_42_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; uint8_t v___x_149_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = lean_unbox(v_a_148_);
lean_dec(v_a_148_);
if (v___x_149_ == 0)
{
goto v___jp_109_;
}
else
{
lean_object* v___x_150_; 
lean_inc_ref(v_b_37_);
v___x_150_ = l_Lean_Meta_isProp(v_b_37_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; uint8_t v___x_152_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = lean_unbox(v_a_151_);
lean_dec(v_a_151_);
if (v___x_152_ == 0)
{
goto v___jp_109_;
}
else
{
lean_object* v___x_153_; 
lean_inc_ref(v_a_36_);
v___x_153_ = l_Lean_Meta_Grind_mkEqTrueProof(v_a_36_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
lean_inc_ref(v_b_37_);
v___x_156_ = l_Lean_mkApp3(v___x_155_, v_a_36_, v_b_37_, v_a_154_);
v___x_157_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_35_, v_b_37_, v___x_156_, v_a_146_, v_a_38_, v_a_40_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_157_;
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_158_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_153_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_153_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_166_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_150_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_150_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec_ref(v_b_37_);
lean_dec_ref(v_a_36_);
lean_dec_ref(v_e_35_);
v_a_174_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_147_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_147_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object* v_e_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_238_, v_a_239_, v_b_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0(lean_object* v_cls_256_, lean_object* v_____do__lift_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_toCold_269_; lean_object* v_options_270_; uint8_t v_hasTrace_271_; 
v_toCold_269_ = lean_ctor_get(v___y_266_, 0);
v_options_270_ = lean_ctor_get(v_toCold_269_, 2);
v_hasTrace_271_ = lean_ctor_get_uint8(v_options_270_, sizeof(void*)*1);
if (v_hasTrace_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_cls_256_);
v___x_272_ = lean_box(v_hasTrace_271_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_275_ = l_Lean_Name_append(v___x_274_, v_cls_256_);
v___x_276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_257_, v_options_270_, v___x_275_);
lean_dec(v___x_275_);
v___x_277_ = lean_box(v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___lam__0___boxed(lean_object* v_cls_279_, lean_object* v_____do__lift_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_279_, v_____do__lift_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v_____do__lift_280_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v_env_300_; uint8_t v___x_301_; lean_object* v_env_302_; lean_object* v___x_303_; lean_object* v_toCold_304_; lean_object* v_mctx_305_; lean_object* v_lctx_306_; lean_object* v_options_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_299_ = lean_st_ref_get(v___y_297_);
v_env_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc_ref(v_env_300_);
lean_dec(v___x_299_);
v___x_301_ = 0;
v_env_302_ = l_Lean_Environment_setRecordingDeps(v_env_300_, v___x_301_);
v___x_303_ = lean_st_ref_get(v___y_295_);
v_toCold_304_ = lean_ctor_get(v___y_296_, 0);
v_mctx_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_mctx_305_);
lean_dec(v___x_303_);
v_lctx_306_ = lean_ctor_get(v___y_294_, 2);
v_options_307_ = lean_ctor_get(v_toCold_304_, 2);
lean_inc_ref(v_options_307_);
lean_inc_ref(v_lctx_306_);
v___x_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_308_, 0, v_env_302_);
lean_ctor_set(v___x_308_, 1, v_mctx_305_);
lean_ctor_set(v___x_308_, 2, v_lctx_306_);
lean_ctor_set(v___x_308_, 3, v_options_307_);
v___x_309_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_msgData_293_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msgData_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_318_; double v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_float_of_nat(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* v_cls_323_, lean_object* v_msg_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_377_; 
v_ref_330_ = lean_ctor_get(v___y_327_, 2);
v___x_331_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_377_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_377_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_377_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v_traceState_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_cache_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_376_; 
v___x_336_ = lean_st_ref_take(v___y_328_);
v_traceState_337_ = lean_ctor_get(v___x_336_, 4);
v_env_338_ = lean_ctor_get(v___x_336_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_336_, 1);
v_ngen_340_ = lean_ctor_get(v___x_336_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_336_, 3);
v_cache_342_ = lean_ctor_get(v___x_336_, 5);
v_recordedDeps_343_ = lean_ctor_get(v___x_336_, 6);
v_messages_344_ = lean_ctor_get(v___x_336_, 7);
v_infoState_345_ = lean_ctor_get(v___x_336_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_336_, 9);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_376_ == 0)
{
v___x_348_ = v___x_336_;
v_isShared_349_ = v_isSharedCheck_376_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
lean_inc(v_cache_342_);
lean_inc(v_traceState_337_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_376_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint64_t v_tid_350_; lean_object* v_traces_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_375_; 
v_tid_350_ = lean_ctor_get_uint64(v_traceState_337_, sizeof(void*)*1);
v_traces_351_ = lean_ctor_get(v_traceState_337_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_traceState_337_);
if (v_isSharedCheck_375_ == 0)
{
v___x_353_ = v_traceState_337_;
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_traces_351_);
lean_dec(v_traceState_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_375_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; double v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_355_ = lean_box(0);
v___x_356_ = lean_box(0);
v___x_357_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
v___x_358_ = 0;
v___x_359_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
v___x_360_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_360_, 0, v_cls_323_);
lean_ctor_set(v___x_360_, 1, v___x_356_);
lean_ctor_set(v___x_360_, 2, v___x_359_);
lean_ctor_set_float(v___x_360_, sizeof(void*)*3, v___x_357_);
lean_ctor_set_float(v___x_360_, sizeof(void*)*3 + 8, v___x_357_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*3 + 16, v___x_358_);
v___x_361_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2));
v___x_362_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v_a_332_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
lean_inc(v_ref_330_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_ref_330_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = l_Lean_PersistentArray_push___redArg(v_traces_351_, v___x_363_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_364_);
v___x_366_ = v___x_353_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_364_);
lean_ctor_set_uint64(v_reuseFailAlloc_374_, sizeof(void*)*1, v_tid_350_);
v___x_366_ = v_reuseFailAlloc_374_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 4, v___x_366_);
v___x_368_ = v___x_348_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_338_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_342_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_373_, 9, v_snapshotTasks_346_);
v___x_368_ = v_reuseFailAlloc_373_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_st_ref_put(v___y_328_, v___x_368_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_355_);
v___x_371_ = v___x_334_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_355_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* v_cls_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_378_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_box(0);
v___x_392_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
v___x_393_ = l_Lean_mkConst(v___x_392_, v___x_391_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7(void){
_start:
{
lean_object* v_cls_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_cls_401_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_402_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_403_ = l_Lean_Name_append(v___x_402_, v_cls_401_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__8));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__10));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__12));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
if (lean_obj_tag(v_e_413_) == 7)
{
lean_object* v_binderName_425_; lean_object* v_binderType_426_; lean_object* v_body_427_; uint8_t v_binderInfo_428_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v_toCold_454_; lean_object* v_inheritedTraceOptions_455_; lean_object* v_cls_456_; uint8_t v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___x_563_; lean_object* v_a_564_; uint8_t v___x_565_; 
v_binderName_425_ = lean_ctor_get(v_e_413_, 0);
v_binderType_426_ = lean_ctor_get(v_e_413_, 1);
v_body_427_ = lean_ctor_get(v_e_413_, 2);
v_binderInfo_428_ = lean_ctor_get_uint8(v_e_413_, sizeof(void*)*3 + 8);
v_toCold_454_ = lean_ctor_get(v_a_422_, 0);
v_inheritedTraceOptions_455_ = lean_ctor_get(v_toCold_454_, 11);
v_cls_456_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_563_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_456_, v_inheritedTraceOptions_455_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = lean_unbox(v_a_564_);
lean_dec(v_a_564_);
if (v___x_565_ == 0)
{
v___y_521_ = v_a_414_;
v___y_522_ = v_a_415_;
v___y_523_ = v_a_416_;
v___y_524_ = v_a_417_;
v___y_525_ = v_a_418_;
v___y_526_ = v_a_419_;
v___y_527_ = v_a_420_;
v___y_528_ = v_a_421_;
v___y_529_ = v_a_422_;
v___y_530_ = v_a_423_;
goto v___jp_520_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Meta_Grind_updateLastTag(v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref_known(v___x_566_, 1);
lean_inc_ref(v_e_413_);
v___x_567_ = l_Lean_MessageData_ofExpr(v_e_413_);
v___x_568_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_456_, v___x_567_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_dec_ref_known(v___x_568_, 1);
v___y_521_ = v_a_414_;
v___y_522_ = v_a_415_;
v___y_523_ = v_a_416_;
v___y_524_ = v_a_417_;
v___y_525_ = v_a_418_;
v___y_526_ = v_a_419_;
v___y_527_ = v_a_420_;
v___y_528_ = v_a_421_;
v___y_529_ = v_a_422_;
v___y_530_ = v_a_423_;
goto v___jp_520_;
}
else
{
lean_dec_ref_known(v_e_413_, 3);
return v___x_568_;
}
}
else
{
lean_dec_ref_known(v_e_413_, 3);
return v___x_566_;
}
}
v___jp_429_:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Simp_Result_getProof(v___y_433_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(v___y_432_);
lean_inc_ref(v_binderType_426_);
v___x_444_ = l_Lean_mkApp5(v___x_443_, v_binderType_426_, v___y_431_, v___y_432_, v___y_430_, v_a_442_);
v___x_445_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_413_, v___y_432_, v___x_444_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec_ref_known(v_e_413_, 3);
v_a_446_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_441_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_441_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_469_; 
lean_inc_ref(v_binderType_426_);
v___x_469_ = l_Lean_Meta_Grind_mkEqTrueProof(v_binderType_426_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_n(v_a_470_, 2);
lean_dec_ref_known(v___x_469_, 1);
lean_inc_ref(v_binderType_426_);
v___x_471_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_426_, v_a_470_);
v___x_472_ = lean_expr_instantiate1(v_body_427_, v___x_471_);
lean_dec_ref(v___x_471_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc(v___y_459_);
v___x_473_ = lean_grind_preprocess(v___x_472_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v_expr_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v_expr_475_ = lean_ctor_get(v_a_474_, 0);
lean_inc_ref(v_expr_475_);
lean_inc_ref(v_body_427_);
lean_inc_ref(v_binderType_426_);
lean_inc(v_binderName_425_);
v___x_476_ = l_Lean_mkLambda(v_binderName_425_, v_binderInfo_428_, v_binderType_426_, v_body_427_);
v___x_477_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_413_, v___y_459_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = lean_box(0);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v_expr_475_);
v___x_480_ = lean_grind_internalize(v_expr_475_, v_a_478_, v___x_479_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_toCold_481_; lean_object* v_options_482_; uint8_t v_hasTrace_483_; 
lean_dec_ref_known(v___x_480_, 1);
v_toCold_481_ = lean_ctor_get(v___y_467_, 0);
v_options_482_ = lean_ctor_get(v_toCold_481_, 2);
v_hasTrace_483_ = lean_ctor_get_uint8(v_options_482_, sizeof(void*)*1);
if (v_hasTrace_483_ == 0)
{
v___y_430_ = v_a_470_;
v___y_431_ = v___x_476_;
v___y_432_ = v_expr_475_;
v___y_433_ = v_a_474_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_459_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_465_;
v___y_438_ = v___y_466_;
v___y_439_ = v___y_467_;
v___y_440_ = v___y_468_;
goto v___jp_429_;
}
else
{
lean_object* v_inheritedTraceOptions_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_inheritedTraceOptions_484_ = lean_ctor_get(v_toCold_481_, 11);
v___x_485_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__7, &l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
v___x_486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_484_, v_options_482_, v___x_485_);
if (v___x_486_ == 0)
{
v___y_430_ = v_a_470_;
v___y_431_ = v___x_476_;
v___y_432_ = v_expr_475_;
v___y_433_ = v_a_474_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_459_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_465_;
v___y_438_ = v___y_466_;
v___y_439_ = v___y_467_;
v___y_440_ = v___y_468_;
goto v___jp_429_;
}
else
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Meta_Grind_updateLastTag(v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v___x_487_, 1);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__9, &l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
lean_inc_ref(v_expr_475_);
v___x_489_ = l_Lean_MessageData_ofExpr(v_expr_475_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__11, &l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_inc_ref(v_e_413_);
v___x_493_ = l_Lean_indentExpr(v_e_413_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_456_, v___x_494_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec_ref_known(v___x_495_, 1);
v___y_430_ = v_a_470_;
v___y_431_ = v___x_476_;
v___y_432_ = v_expr_475_;
v___y_433_ = v_a_474_;
v___y_434_ = v___y_458_;
v___y_435_ = v___y_459_;
v___y_436_ = v___y_461_;
v___y_437_ = v___y_465_;
v___y_438_ = v___y_466_;
v___y_439_ = v___y_467_;
v___y_440_ = v___y_468_;
goto v___jp_429_;
}
else
{
lean_dec_ref(v___x_476_);
lean_dec_ref(v_expr_475_);
lean_dec(v_a_474_);
lean_dec(v_a_470_);
lean_dec_ref_known(v_e_413_, 3);
return v___x_495_;
}
}
else
{
lean_dec_ref(v___x_476_);
lean_dec_ref(v_expr_475_);
lean_dec(v_a_474_);
lean_dec(v_a_470_);
lean_dec_ref_known(v_e_413_, 3);
return v___x_487_;
}
}
}
}
else
{
lean_dec_ref(v___x_476_);
lean_dec_ref(v_expr_475_);
lean_dec(v_a_474_);
lean_dec(v_a_470_);
lean_dec_ref_known(v_e_413_, 3);
return v___x_480_;
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___x_476_);
lean_dec_ref(v_expr_475_);
lean_dec(v_a_474_);
lean_dec(v_a_470_);
lean_dec_ref_known(v_e_413_, 3);
v_a_496_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_477_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_477_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_a_470_);
lean_dec_ref_known(v_e_413_, 3);
v_a_504_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_473_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_473_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref_known(v_e_413_, 3);
v_a_512_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_469_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_469_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
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
v___jp_520_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Expr_hasLooseBVars(v_body_427_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_inc_ref(v_body_427_);
lean_inc_ref(v_binderType_426_);
v___x_532_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_413_, v_binderType_426_, v_body_427_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_532_;
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = 0;
lean_inc_ref(v_binderType_426_);
v___x_534_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_426_, v___y_521_, v___y_525_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_554_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_554_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_554_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_554_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_542_; 
lean_dec_ref_known(v_e_413_, 3);
v___x_540_ = lean_box(0);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_toCold_544_; lean_object* v_inheritedTraceOptions_545_; lean_object* v___x_546_; lean_object* v_a_547_; uint8_t v___x_548_; 
lean_del_object(v___x_537_);
v_toCold_544_ = lean_ctor_get(v___y_529_, 0);
v_inheritedTraceOptions_545_ = lean_ctor_get(v_toCold_544_, 11);
v___x_546_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_456_, v_inheritedTraceOptions_545_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_548_ == 0)
{
v___y_458_ = v___x_533_;
v___y_459_ = v___y_521_;
v___y_460_ = v___y_522_;
v___y_461_ = v___y_523_;
v___y_462_ = v___y_524_;
v___y_463_ = v___y_525_;
v___y_464_ = v___y_526_;
v___y_465_ = v___y_527_;
v___y_466_ = v___y_528_;
v___y_467_ = v___y_529_;
v___y_468_ = v___y_530_;
goto v___jp_457_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Grind_updateLastTag(v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec_ref_known(v___x_549_, 1);
v___x_550_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__13, &l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
lean_inc_ref(v_e_413_);
v___x_551_ = l_Lean_MessageData_ofExpr(v_e_413_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_456_, v___x_552_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_dec_ref_known(v___x_553_, 1);
v___y_458_ = v___x_533_;
v___y_459_ = v___y_521_;
v___y_460_ = v___y_522_;
v___y_461_ = v___y_523_;
v___y_462_ = v___y_524_;
v___y_463_ = v___y_525_;
v___y_464_ = v___y_526_;
v___y_465_ = v___y_527_;
v___y_466_ = v___y_528_;
v___y_467_ = v___y_529_;
v___y_468_ = v___y_530_;
goto v___jp_457_;
}
else
{
lean_dec_ref_known(v_e_413_, 3);
return v___x_553_;
}
}
else
{
lean_dec_ref_known(v_e_413_, 3);
return v___x_549_;
}
}
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref_known(v_e_413_, 3);
v_a_555_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_534_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_534_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec_ref(v_e_413_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Grind_propagateForallPropUp(v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* v_cls_584_, lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_584_, v_msg_585_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* v_cls_598_, lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(v_cls_598_, v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* v_origin_614_, lean_object* v_proof_615_, lean_object* v_kind_616_, lean_object* v_prios_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; uint8_t v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_624_ = 0;
v___x_625_ = 1;
v___x_626_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v_origin_614_, v___x_623_, v_proof_615_, v_kind_616_, v_prios_617_, v___x_624_, v___x_624_, v___x_625_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_626_) == 0)
{
return v___x_626_;
}
else
{
lean_object* v_a_627_; uint8_t v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v___x_628_ = l_Lean_Exception_isInterrupt(v_a_627_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
lean_inc(v_a_627_);
v___x_629_ = l_Lean_Exception_isRuntime(v_a_627_);
if (v___x_629_ == 0)
{
lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_626_, 0);
lean_dec(v_unused_638_);
v___x_631_ = v___x_626_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_dec(v___x_626_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 0);
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
return v___x_626_;
}
}
else
{
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* v_origin_639_, lean_object* v_proof_640_, lean_object* v_kind_641_, lean_object* v_prios_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_639_, v_proof_640_, v_kind_641_, v_prios_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_648_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
if (lean_obj_tag(v_x_650_) == 0)
{
uint8_t v___x_651_; 
v___x_651_ = 1;
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
else
{
if (lean_obj_tag(v_x_650_) == 0)
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
else
{
lean_object* v_head_654_; lean_object* v_tail_655_; lean_object* v_head_656_; lean_object* v_tail_657_; uint8_t v___x_658_; 
v_head_654_ = lean_ctor_get(v_x_649_, 0);
v_tail_655_ = lean_ctor_get(v_x_649_, 1);
v_head_656_ = lean_ctor_get(v_x_650_, 0);
v_tail_657_ = lean_ctor_get(v_x_650_, 1);
v___x_658_ = lean_expr_eqv(v_head_654_, v_head_656_);
if (v___x_658_ == 0)
{
return v___x_658_;
}
else
{
v_x_649_ = v_tail_655_;
v_x_650_ = v_tail_657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec(v_x_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* v_thm_x27_664_, lean_object* v_as_665_, size_t v_i_666_, size_t v_stop_667_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_666_, v_stop_667_);
if (v___x_668_ == 0)
{
lean_object* v_patterns_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_patterns_669_ = lean_ctor_get(v_thm_x27_664_, 3);
v___x_670_ = lean_array_uget_borrowed(v_as_665_, v_i_666_);
v___x_671_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_669_, v___x_670_);
if (v___x_671_ == 0)
{
size_t v___x_672_; size_t v___x_673_; 
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_666_, v___x_672_);
v_i_666_ = v___x_673_;
goto _start;
}
else
{
return v___x_671_;
}
}
else
{
uint8_t v___x_675_; 
v___x_675_ = 0;
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* v_thm_x27_676_, lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_){
_start:
{
size_t v_i_boxed_680_; size_t v_stop_boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v_i_boxed_680_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_681_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_676_, v_as_677_, v_i_boxed_680_, v_stop_boxed_681_);
lean_dec_ref(v_as_677_);
lean_dec_ref(v_thm_x27_676_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* v_patternsFoundSoFar_684_, lean_object* v_thm_x27_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_patternsFoundSoFar_684_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
v___x_689_ = 1;
return v___x_689_;
}
else
{
if (v___x_688_ == 0)
{
return v___x_688_;
}
else
{
size_t v___x_690_; size_t v___x_691_; uint8_t v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_687_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_685_, v_patternsFoundSoFar_684_, v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
return v___x_688_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* v_patternsFoundSoFar_694_, lean_object* v_thm_x27_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_694_, v_thm_x27_695_);
lean_dec_ref(v_thm_x27_695_);
lean_dec_ref(v_patternsFoundSoFar_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(lean_object* v_proof_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___y_714_; lean_object* v___x_782_; 
lean_inc_ref(v_proof_709_);
v___x_782_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_709_, v_a_711_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___x_784_ = l_Lean_Expr_cleanupAnnotations(v_a_783_);
lean_dec(v_a_783_);
v___x_785_ = l_Lean_Expr_isApp(v___x_784_);
if (v___x_785_ == 0)
{
lean_dec_ref(v___x_784_);
v___y_714_ = v_a_710_;
goto v___jp_713_;
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_784_);
v___x_787_ = l_Lean_Expr_isApp(v___x_786_);
if (v___x_787_ == 0)
{
lean_dec_ref(v___x_786_);
lean_dec_ref(v___x_784_);
v___y_714_ = v_a_710_;
goto v___jp_713_;
}
else
{
lean_object* v_arg_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_arg_788_ = lean_ctor_get(v___x_784_, 1);
lean_inc_ref(v_arg_788_);
lean_dec_ref(v___x_784_);
v___x_789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_786_);
lean_dec_ref(v___x_786_);
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3));
v___x_791_ = l_Lean_Expr_isConstOf(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
uint8_t v___x_792_; 
v___x_792_ = l_Lean_Expr_isApp(v___x_789_);
if (v___x_792_ == 0)
{
lean_dec_ref(v___x_789_);
lean_dec_ref(v_arg_788_);
v___y_714_ = v_a_710_;
goto v___jp_713_;
}
else
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_789_);
lean_dec_ref(v___x_789_);
v___x_794_ = l_Lean_Expr_isApp(v___x_793_);
if (v___x_794_ == 0)
{
lean_dec_ref(v___x_793_);
lean_dec_ref(v_arg_788_);
v___y_714_ = v_a_710_;
goto v___jp_713_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_793_);
lean_dec_ref(v___x_793_);
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6));
v___x_797_ = l_Lean_Expr_isConstOf(v___x_795_, v___x_796_);
lean_dec_ref(v___x_795_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_arg_788_);
v___y_714_ = v_a_710_;
goto v___jp_713_;
}
else
{
lean_dec_ref(v_proof_709_);
v_proof_709_ = v_arg_788_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v___x_789_);
lean_dec_ref(v_proof_709_);
v_proof_709_ = v_arg_788_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_proof_709_);
v_a_800_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_782_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_782_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
v___jp_713_:
{
if (lean_obj_tag(v_proof_709_) == 1)
{
lean_object* v_fvarId_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_fvarId_715_ = lean_ctor_get(v_proof_709_, 0);
lean_inc(v_fvarId_715_);
lean_dec_ref_known(v_proof_709_, 1);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v_fvarId_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v_toGoalState_719_; lean_object* v_ematch_720_; lean_object* v_mvarId_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_proof_709_);
v___x_718_ = lean_st_ref_take(v___y_714_);
v_toGoalState_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc_ref(v_toGoalState_719_);
v_ematch_720_ = lean_ctor_get(v_toGoalState_719_, 13);
lean_inc_ref(v_ematch_720_);
v_mvarId_721_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_781_);
v___x_723_ = v___x_718_;
v_isShared_724_ = v_isSharedCheck_780_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_mvarId_721_);
lean_dec(v___x_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_780_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_nextDeclIdx_725_; lean_object* v_enodeMap_726_; lean_object* v_exprs_727_; lean_object* v_parents_728_; lean_object* v_congrTable_729_; lean_object* v_appMap_730_; lean_object* v_indicesFound_731_; lean_object* v_toProcess_732_; lean_object* v_internalizing_733_; uint8_t v_inconsistent_734_; lean_object* v_nextIdx_735_; lean_object* v_newRawFacts_736_; lean_object* v_facts_737_; lean_object* v_extThms_738_; lean_object* v_inj_739_; lean_object* v_split_740_; lean_object* v_clean_741_; lean_object* v_sstates_742_; lean_object* v_goalStack_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_778_; 
v_nextDeclIdx_725_ = lean_ctor_get(v_toGoalState_719_, 0);
v_enodeMap_726_ = lean_ctor_get(v_toGoalState_719_, 1);
v_exprs_727_ = lean_ctor_get(v_toGoalState_719_, 2);
v_parents_728_ = lean_ctor_get(v_toGoalState_719_, 3);
v_congrTable_729_ = lean_ctor_get(v_toGoalState_719_, 4);
v_appMap_730_ = lean_ctor_get(v_toGoalState_719_, 5);
v_indicesFound_731_ = lean_ctor_get(v_toGoalState_719_, 6);
v_toProcess_732_ = lean_ctor_get(v_toGoalState_719_, 7);
v_internalizing_733_ = lean_ctor_get(v_toGoalState_719_, 8);
v_inconsistent_734_ = lean_ctor_get_uint8(v_toGoalState_719_, sizeof(void*)*19);
v_nextIdx_735_ = lean_ctor_get(v_toGoalState_719_, 9);
v_newRawFacts_736_ = lean_ctor_get(v_toGoalState_719_, 10);
v_facts_737_ = lean_ctor_get(v_toGoalState_719_, 11);
v_extThms_738_ = lean_ctor_get(v_toGoalState_719_, 12);
v_inj_739_ = lean_ctor_get(v_toGoalState_719_, 14);
v_split_740_ = lean_ctor_get(v_toGoalState_719_, 15);
v_clean_741_ = lean_ctor_get(v_toGoalState_719_, 16);
v_sstates_742_ = lean_ctor_get(v_toGoalState_719_, 17);
v_goalStack_743_ = lean_ctor_get(v_toGoalState_719_, 18);
v_isSharedCheck_778_ = !lean_is_exclusive(v_toGoalState_719_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_toGoalState_719_, 13);
lean_dec(v_unused_779_);
v___x_745_ = v_toGoalState_719_;
v_isShared_746_ = v_isSharedCheck_778_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_goalStack_743_);
lean_inc(v_sstates_742_);
lean_inc(v_clean_741_);
lean_inc(v_split_740_);
lean_inc(v_inj_739_);
lean_inc(v_extThms_738_);
lean_inc(v_facts_737_);
lean_inc(v_newRawFacts_736_);
lean_inc(v_nextIdx_735_);
lean_inc(v_internalizing_733_);
lean_inc(v_toProcess_732_);
lean_inc(v_indicesFound_731_);
lean_inc(v_appMap_730_);
lean_inc(v_congrTable_729_);
lean_inc(v_parents_728_);
lean_inc(v_exprs_727_);
lean_inc(v_enodeMap_726_);
lean_inc(v_nextDeclIdx_725_);
lean_dec(v_toGoalState_719_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_778_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_thmMap_747_; lean_object* v_gmt_748_; lean_object* v_thms_749_; lean_object* v_newThms_750_; lean_object* v_numInstances_751_; lean_object* v_numDelayedInstances_752_; lean_object* v_num_753_; lean_object* v_preInstances_754_; lean_object* v_nextThmIdx_755_; lean_object* v_matchEqNames_756_; lean_object* v_delayedThmInsts_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_777_; 
v_thmMap_747_ = lean_ctor_get(v_ematch_720_, 0);
v_gmt_748_ = lean_ctor_get(v_ematch_720_, 1);
v_thms_749_ = lean_ctor_get(v_ematch_720_, 2);
v_newThms_750_ = lean_ctor_get(v_ematch_720_, 3);
v_numInstances_751_ = lean_ctor_get(v_ematch_720_, 4);
v_numDelayedInstances_752_ = lean_ctor_get(v_ematch_720_, 5);
v_num_753_ = lean_ctor_get(v_ematch_720_, 6);
v_preInstances_754_ = lean_ctor_get(v_ematch_720_, 7);
v_nextThmIdx_755_ = lean_ctor_get(v_ematch_720_, 8);
v_matchEqNames_756_ = lean_ctor_get(v_ematch_720_, 9);
v_delayedThmInsts_757_ = lean_ctor_get(v_ematch_720_, 10);
v_isSharedCheck_777_ = !lean_is_exclusive(v_ematch_720_);
if (v_isSharedCheck_777_ == 0)
{
v___x_759_ = v_ematch_720_;
v_isShared_760_ = v_isSharedCheck_777_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_delayedThmInsts_757_);
lean_inc(v_matchEqNames_756_);
lean_inc(v_nextThmIdx_755_);
lean_inc(v_preInstances_754_);
lean_inc(v_num_753_);
lean_inc(v_numDelayedInstances_752_);
lean_inc(v_numInstances_751_);
lean_inc(v_newThms_750_);
lean_inc(v_thms_749_);
lean_inc(v_gmt_748_);
lean_inc(v_thmMap_747_);
lean_dec(v_ematch_720_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_777_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_nextThmIdx_755_, v___x_761_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 8, v___x_762_);
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_thmMap_747_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_gmt_748_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_thms_749_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_newThms_750_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_numInstances_751_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v_numDelayedInstances_752_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_num_753_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_preInstances_754_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 9, v_matchEqNames_756_);
lean_ctor_set(v_reuseFailAlloc_776_, 10, v_delayedThmInsts_757_);
v___x_764_ = v_reuseFailAlloc_776_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 13, v___x_764_);
v___x_766_ = v___x_745_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_nextDeclIdx_725_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_enodeMap_726_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_exprs_727_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_parents_728_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_congrTable_729_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_appMap_730_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_indicesFound_731_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v_toProcess_732_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_internalizing_733_);
lean_ctor_set(v_reuseFailAlloc_775_, 9, v_nextIdx_735_);
lean_ctor_set(v_reuseFailAlloc_775_, 10, v_newRawFacts_736_);
lean_ctor_set(v_reuseFailAlloc_775_, 11, v_facts_737_);
lean_ctor_set(v_reuseFailAlloc_775_, 12, v_extThms_738_);
lean_ctor_set(v_reuseFailAlloc_775_, 13, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 14, v_inj_739_);
lean_ctor_set(v_reuseFailAlloc_775_, 15, v_split_740_);
lean_ctor_set(v_reuseFailAlloc_775_, 16, v_clean_741_);
lean_ctor_set(v_reuseFailAlloc_775_, 17, v_sstates_742_);
lean_ctor_set(v_reuseFailAlloc_775_, 18, v_goalStack_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_775_, sizeof(void*)*19, v_inconsistent_734_);
v___x_766_ = v_reuseFailAlloc_775_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_766_);
v___x_768_ = v___x_723_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_mvarId_721_);
v___x_768_ = v_reuseFailAlloc_774_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_769_ = lean_st_ref_put(v___y_714_, v___x_768_);
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1));
v___x_771_ = lean_name_append_index_after(v___x_770_, v_nextThmIdx_755_);
v___x_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(lean_object* v_proof_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(lean_object* v_proof_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_813_, v_a_814_, v_a_821_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(lean_object* v_proof_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(v_proof_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
return v_res_838_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t v_a_839_, lean_object* v_as_840_, size_t v_i_841_, size_t v_stop_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_eq(v_i_841_, v_stop_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_uget_borrowed(v_as_840_, v_i_841_);
v___x_845_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_844_, v_a_839_);
if (v___x_845_ == 0)
{
size_t v___x_846_; size_t v___x_847_; 
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_841_, v___x_846_);
v_i_841_ = v___x_847_;
goto _start;
}
else
{
return v___x_845_;
}
}
else
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* v_a_850_, lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_){
_start:
{
uint64_t v_a_3837__boxed_854_; size_t v_i_boxed_855_; size_t v_stop_boxed_856_; uint8_t v_res_857_; lean_object* v_r_858_; 
v_a_3837__boxed_854_ = lean_unbox_uint64(v_a_850_);
lean_dec_ref(v_a_850_);
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_3837__boxed_854_, v_as_851_, v_i_boxed_855_, v_stop_boxed_856_);
lean_dec_ref(v_as_851_);
v_r_858_ = lean_box(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* v_proof_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_861_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_924_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_924_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_924_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_875_; lean_object* v___x_876_; 
lean_del_object(v___x_873_);
v_val_875_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v_a_871_, 1);
lean_inc(v_a_868_);
lean_inc_ref(v_a_867_);
lean_inc(v_a_866_);
lean_inc_ref(v_a_865_);
v___x_876_ = lean_infer_type(v_proof_859_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = l_Lean_Meta_Grind_getAnchor(v_a_877_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_902_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_902_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_val_875_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec(v_a_879_);
lean_dec(v_val_875_);
v___x_886_ = lean_box(v___x_885_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_886_);
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
if (v___x_885_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v_a_879_);
lean_dec(v_val_875_);
v___x_890_ = lean_box(v___x_885_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_890_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
size_t v___x_894_; size_t v___x_895_; uint64_t v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_894_ = ((size_t)0ULL);
v___x_895_ = lean_usize_of_nat(v___x_884_);
v___x_896_ = lean_unbox_uint64(v_a_879_);
lean_dec(v_a_879_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_896_, v_val_875_, v___x_894_, v___x_895_);
lean_dec(v_val_875_);
v___x_898_ = lean_box(v___x_897_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_898_);
v___x_900_ = v___x_881_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_val_875_);
v_a_903_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_878_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_878_);
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
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_val_875_);
v_a_911_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_876_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_876_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_a_871_);
lean_dec_ref(v_proof_859_);
v___x_919_ = 1;
v___x_920_ = lean_box(v___x_919_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_920_);
v___x_922_ = v___x_873_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_proof_859_);
v_a_925_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_870_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_870_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* v_proof_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* v_a_945_, lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_a_962_; uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v_a_945_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_b_949_);
return v___x_967_;
}
else
{
lean_object* v_a_968_; uint8_t v___x_969_; 
v_a_968_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
v___x_969_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_b_949_, v_a_968_);
if (v___x_969_ == 0)
{
v_a_962_ = v_b_949_;
goto v___jp_961_;
}
else
{
lean_object* v___x_970_; 
lean_inc(v_a_945_);
lean_inc(v_a_968_);
v___x_970_ = l_Lean_Meta_Grind_activateTheorem(v_a_968_, v_a_945_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_patterns_971_; lean_object* v___x_972_; 
lean_dec_ref_known(v___x_970_, 1);
v_patterns_971_ = lean_ctor_get(v_a_968_, 3);
lean_inc(v_patterns_971_);
v___x_972_ = lean_array_push(v_b_949_, v_patterns_971_);
v_a_962_ = v___x_972_;
goto v___jp_961_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_b_949_);
lean_dec(v_a_945_);
v_a_973_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_970_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
v___jp_961_:
{
size_t v___x_963_; size_t v___x_964_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_948_, v___x_963_);
v_i_948_ = v___x_964_;
v_b_949_ = v_a_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* v_a_981_, lean_object* v_as_982_, lean_object* v_sz_983_, lean_object* v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_983_);
lean_dec(v_sz_983_);
v_i_boxed_998_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_981_, v_as_982_, v_sz_boxed_997_, v_i_boxed_998_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v_as_982_);
return v_res_999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
lean_inc_ref(v_e_1007_);
v___x_1019_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_n(v_a_1020_, 2);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_a_1020_, v_a_1008_, v_a_1015_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
lean_inc_ref(v_e_1007_);
v___x_1023_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1007_, v_a_1020_);
lean_inc_ref(v___x_1023_);
v___x_1024_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v___x_1023_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1204_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1204_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1204_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_unbox(v_a_1025_);
lean_dec(v_a_1025_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v___x_1030_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v_toGoalState_1035_; lean_object* v_ematch_1036_; lean_object* v_newThms_1037_; lean_object* v_size_1038_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___x_1087_; 
v___x_1034_ = lean_st_ref_get(v_a_1008_);
v_toGoalState_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_toGoalState_1035_);
lean_dec(v___x_1034_);
v_ematch_1036_ = lean_ctor_get(v_toGoalState_1035_, 13);
lean_inc_ref(v_ematch_1036_);
lean_dec_ref(v_toGoalState_1035_);
v_newThms_1037_ = lean_ctor_get(v_ematch_1036_, 3);
lean_inc_ref(v_newThms_1037_);
lean_dec_ref(v_ematch_1036_);
v_size_1038_ = lean_ctor_get(v_newThms_1037_, 2);
lean_inc(v_size_1038_);
lean_dec_ref(v_newThms_1037_);
v___x_1087_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1007_, v_a_1008_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2));
v___x_1090_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v_a_1010_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v_patternsFoundSoFar_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___x_1150_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc_n(v_a_1091_, 2);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_unsigned_to_nat(1000u);
v___x_1093_ = 0;
lean_inc_ref(v___x_1023_);
lean_inc(v_a_1022_);
v___x_1150_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(v_a_1022_, v___x_1089_, v___x_1023_, v___x_1092_, v_a_1091_, v___x_1093_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; size_t v_sz_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v_sz_1152_ = lean_array_size(v_a_1151_);
v___x_1153_ = ((size_t)0ULL);
lean_inc(v_a_1088_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_1088_, v_a_1151_, v_sz_1152_, v___x_1153_, v___x_1089_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1151_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = lean_box(6);
lean_inc(v_a_1091_);
lean_inc_ref(v___x_1023_);
lean_inc(v_a_1022_);
v___x_1157_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_1022_, v___x_1023_, v___x_1156_, v_a_1091_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
if (lean_obj_tag(v_a_1158_) == 1)
{
lean_object* v_val_1159_; uint8_t v___x_1160_; 
v_val_1159_ = lean_ctor_get(v_a_1158_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v_a_1158_, 1);
v___x_1160_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_a_1155_, v_val_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v_val_1159_);
v_patternsFoundSoFar_1125_ = v_a_1155_;
v___y_1126_ = v_a_1008_;
v___y_1127_ = v_a_1009_;
v___y_1128_ = v_a_1010_;
v___y_1129_ = v_a_1011_;
v___y_1130_ = v_a_1012_;
v___y_1131_ = v_a_1013_;
v___y_1132_ = v_a_1014_;
v___y_1133_ = v_a_1015_;
v___y_1134_ = v_a_1016_;
v___y_1135_ = v_a_1017_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1161_; 
lean_inc(v_a_1088_);
lean_inc(v_val_1159_);
v___x_1161_ = l_Lean_Meta_Grind_activateTheorem(v_val_1159_, v_a_1088_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_patterns_1162_; lean_object* v___x_1163_; 
lean_dec_ref_known(v___x_1161_, 1);
v_patterns_1162_ = lean_ctor_get(v_val_1159_, 3);
lean_inc(v_patterns_1162_);
lean_dec(v_val_1159_);
v___x_1163_ = lean_array_push(v_a_1155_, v_patterns_1162_);
v_patternsFoundSoFar_1125_ = v___x_1163_;
v___y_1126_ = v_a_1008_;
v___y_1127_ = v_a_1009_;
v___y_1128_ = v_a_1010_;
v___y_1129_ = v_a_1011_;
v___y_1130_ = v_a_1012_;
v___y_1131_ = v_a_1013_;
v___y_1132_ = v_a_1014_;
v___y_1133_ = v_a_1015_;
v___y_1134_ = v_a_1016_;
v___y_1135_ = v_a_1017_;
goto v___jp_1124_;
}
else
{
lean_dec(v_val_1159_);
lean_dec(v_a_1155_);
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
return v___x_1161_;
}
}
}
else
{
lean_dec(v_a_1158_);
v_patternsFoundSoFar_1125_ = v_a_1155_;
v___y_1126_ = v_a_1008_;
v___y_1127_ = v_a_1009_;
v___y_1128_ = v_a_1010_;
v___y_1129_ = v_a_1011_;
v___y_1130_ = v_a_1012_;
v___y_1131_ = v_a_1013_;
v___y_1132_ = v_a_1014_;
v___y_1133_ = v_a_1015_;
v___y_1134_ = v_a_1016_;
v___y_1135_ = v_a_1017_;
goto v___jp_1124_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1155_);
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1164_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1157_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1157_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1172_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1154_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1154_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1180_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1150_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1150_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
v___jp_1094_:
{
lean_object* v___x_1105_; lean_object* v_toGoalState_1106_; lean_object* v_ematch_1107_; lean_object* v_newThms_1108_; lean_object* v_size_1109_; uint8_t v___x_1110_; 
v___x_1105_ = lean_st_ref_get(v___y_1095_);
v_toGoalState_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_toGoalState_1106_);
lean_dec(v___x_1105_);
v_ematch_1107_ = lean_ctor_get(v_toGoalState_1106_, 13);
lean_inc_ref(v_ematch_1107_);
lean_dec_ref(v_toGoalState_1106_);
v_newThms_1108_ = lean_ctor_get(v_ematch_1107_, 3);
lean_inc_ref(v_newThms_1108_);
lean_dec_ref(v_ematch_1107_);
v_size_1109_ = lean_ctor_get(v_newThms_1108_, 2);
lean_inc(v_size_1109_);
lean_dec_ref(v_newThms_1108_);
v___x_1110_ = lean_nat_dec_eq(v_size_1109_, v_size_1038_);
lean_dec(v_size_1109_);
if (v___x_1110_ == 0)
{
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
v___y_1040_ = v___y_1095_;
v___y_1041_ = v___y_1099_;
v___y_1042_ = v___y_1100_;
v___y_1043_ = v___y_1101_;
v___y_1044_ = v___y_1102_;
v___y_1045_ = v___y_1103_;
v___y_1046_ = v___y_1104_;
goto v___jp_1039_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3));
v___x_1112_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_1022_, v___x_1023_, v___x_1111_, v_a_1091_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
if (lean_obj_tag(v_a_1113_) == 1)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
v_val_1114_ = lean_ctor_get(v_a_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_a_1113_, 1);
v___x_1115_ = l_Lean_Meta_Grind_activateTheorem(v_val_1114_, v_a_1088_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref_known(v___x_1115_, 1);
v___y_1040_ = v___y_1095_;
v___y_1041_ = v___y_1099_;
v___y_1042_ = v___y_1100_;
v___y_1043_ = v___y_1101_;
v___y_1044_ = v___y_1102_;
v___y_1045_ = v___y_1103_;
v___y_1046_ = v___y_1104_;
goto v___jp_1039_;
}
else
{
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v_e_1007_);
return v___x_1115_;
}
}
else
{
lean_dec(v_a_1113_);
lean_dec(v_a_1088_);
v___y_1040_ = v___y_1095_;
v___y_1041_ = v___y_1099_;
v___y_1042_ = v___y_1100_;
v___y_1043_ = v___y_1101_;
v___y_1044_ = v___y_1102_;
v___y_1045_ = v___y_1103_;
v___y_1046_ = v___y_1104_;
goto v___jp_1039_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v_e_1007_);
v_a_1116_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1112_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1112_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
v___jp_1124_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_box(7);
lean_inc(v_a_1091_);
lean_inc_ref(v___x_1023_);
lean_inc(v_a_1022_);
v___x_1137_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_1022_, v___x_1023_, v___x_1136_, v_a_1091_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
if (lean_obj_tag(v_a_1138_) == 1)
{
lean_object* v_val_1139_; uint8_t v___x_1140_; 
v_val_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v_a_1138_, 1);
v___x_1140_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_1125_, v_val_1139_);
lean_dec_ref(v_patternsFoundSoFar_1125_);
if (v___x_1140_ == 0)
{
lean_dec(v_val_1139_);
v___y_1095_ = v___y_1126_;
v___y_1096_ = v___y_1127_;
v___y_1097_ = v___y_1128_;
v___y_1098_ = v___y_1129_;
v___y_1099_ = v___y_1130_;
v___y_1100_ = v___y_1131_;
v___y_1101_ = v___y_1132_;
v___y_1102_ = v___y_1133_;
v___y_1103_ = v___y_1134_;
v___y_1104_ = v___y_1135_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1141_; 
lean_inc(v_a_1088_);
v___x_1141_ = l_Lean_Meta_Grind_activateTheorem(v_val_1139_, v_a_1088_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_dec_ref_known(v___x_1141_, 1);
v___y_1095_ = v___y_1126_;
v___y_1096_ = v___y_1127_;
v___y_1097_ = v___y_1128_;
v___y_1098_ = v___y_1129_;
v___y_1099_ = v___y_1130_;
v___y_1100_ = v___y_1131_;
v___y_1101_ = v___y_1132_;
v___y_1102_ = v___y_1133_;
v___y_1103_ = v___y_1134_;
v___y_1104_ = v___y_1135_;
goto v___jp_1094_;
}
else
{
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
return v___x_1141_;
}
}
}
else
{
lean_dec(v_a_1138_);
lean_dec_ref(v_patternsFoundSoFar_1125_);
v___y_1095_ = v___y_1126_;
v___y_1096_ = v___y_1127_;
v___y_1097_ = v___y_1128_;
v___y_1098_ = v___y_1129_;
v___y_1099_ = v___y_1130_;
v___y_1100_ = v___y_1131_;
v___y_1101_ = v___y_1132_;
v___y_1102_ = v___y_1133_;
v___y_1103_ = v___y_1134_;
v___y_1104_ = v___y_1135_;
goto v___jp_1094_;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_patternsFoundSoFar_1125_);
lean_dec(v_a_1091_);
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1142_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1137_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1137_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1088_);
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1188_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1090_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1090_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_size_1038_);
lean_del_object(v___x_1027_);
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1196_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1087_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1087_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
v___jp_1039_:
{
lean_object* v___x_1047_; lean_object* v_toGoalState_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1085_; 
v___x_1047_ = lean_st_ref_get(v___y_1040_);
v_toGoalState_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_1047_, 1);
lean_dec(v_unused_1086_);
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1085_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_toGoalState_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1085_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_ematch_1052_; lean_object* v_newThms_1053_; lean_object* v_size_1054_; uint8_t v___x_1055_; 
v_ematch_1052_ = lean_ctor_get(v_toGoalState_1048_, 13);
lean_inc_ref(v_ematch_1052_);
lean_dec_ref(v_toGoalState_1048_);
v_newThms_1053_ = lean_ctor_get(v_ematch_1052_, 3);
lean_inc_ref(v_newThms_1053_);
lean_dec_ref(v_ematch_1052_);
v_size_1054_ = lean_ctor_get(v_newThms_1053_, 2);
lean_inc(v_size_1054_);
lean_dec_ref(v_newThms_1053_);
v___x_1055_ = lean_nat_dec_eq(v_size_1054_, v_size_1038_);
lean_dec(v_size_1038_);
lean_dec(v_size_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_del_object(v___x_1050_);
lean_dec_ref(v_e_1007_);
v___x_1056_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1056_);
v___x_1058_ = v___x_1027_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_del_object(v___x_1027_);
v___x_1060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
v___x_1061_ = l_Lean_indentExpr(v_e_1007_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 7);
lean_ctor_set(v___x_1050_, 1, v___x_1061_);
lean_ctor_set(v___x_1050_, 0, v___x_1060_);
v___x_1063_ = v___x_1050_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1041_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
uint8_t v_verbose_1069_; 
v_verbose_1069_ = lean_ctor_get_uint8(v_a_1065_, 0);
lean_dec(v_a_1065_);
if (v_verbose_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec_ref(v___x_1063_);
v___x_1070_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
lean_object* v___x_1074_; 
lean_del_object(v___x_1067_);
v___x_1074_ = l_Lean_Meta_Sym_reportIssue(v___x_1063_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v___x_1063_);
v_a_1076_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1064_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1064_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
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
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v___x_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_e_1007_);
v_a_1205_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1024_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1024_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1020_);
lean_dec_ref(v_e_1007_);
v_a_1213_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1021_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1021_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_e_1007_);
v_a_1221_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1019_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1019_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
return v_res_1241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1247_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_1248_ = l_Lean_Name_append(v___x_1247_, v___x_1246_);
return v___x_1248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__3));
v___x_1251_ = l_Lean_stringToMessageData(v___x_1250_);
return v___x_1251_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__10));
v___x_1267_ = l_Lean_mkConst(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__13));
v___x_1275_ = l_Lean_mkConst(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
if (lean_obj_tag(v_e_1276_) == 7)
{
lean_object* v_binderName_1291_; lean_object* v_binderType_1292_; lean_object* v_body_1293_; uint8_t v_binderInfo_1294_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___x_1391_; 
v_binderName_1291_ = lean_ctor_get(v_e_1276_, 0);
v_binderType_1292_ = lean_ctor_get(v_e_1276_, 1);
v_body_1293_ = lean_ctor_get(v_e_1276_, 2);
v_binderInfo_1294_ = lean_ctor_get_uint8(v_e_1276_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_1276_);
v___x_1391_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1276_, v_a_1277_, v_a_1281_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; uint8_t v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = lean_unbox(v_a_1392_);
lean_dec(v_a_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_inc_ref(v_e_1276_);
v___x_1394_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1276_, v_a_1277_, v_a_1281_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1479_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1479_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1479_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec_ref_known(v_e_1276_, 3);
v___x_1400_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1400_);
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v___x_1404_; 
lean_del_object(v___x_1397_);
lean_inc_ref(v_e_1276_);
v___x_1404_ = l_Lean_Meta_Grind_eqResolution(v_e_1276_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
if (lean_obj_tag(v_a_1405_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1470_; 
v_val_1406_ = lean_ctor_get(v_a_1405_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_a_1405_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1408_ = v_a_1405_;
v_isShared_1409_ = v_isSharedCheck_1470_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v_a_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1470_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_fst_1410_; lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1469_; 
v_fst_1410_ = lean_ctor_get(v_val_1406_, 0);
v_snd_1411_ = lean_ctor_get(v_val_1406_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_val_1406_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1413_ = v_val_1406_;
v_isShared_1414_ = v_isSharedCheck_1469_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_inc(v_fst_1410_);
lean_dec(v_val_1406_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1469_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v_toCold_1453_; lean_object* v_options_1454_; uint8_t v_hasTrace_1455_; 
v_toCold_1453_ = lean_ctor_get(v_a_1285_, 0);
v_options_1454_ = lean_ctor_get(v_toCold_1453_, 2);
v_hasTrace_1455_ = lean_ctor_get_uint8(v_options_1454_, sizeof(void*)*1);
if (v_hasTrace_1455_ == 0)
{
lean_del_object(v___x_1413_);
v___y_1416_ = v_a_1277_;
v___y_1417_ = v_a_1278_;
v___y_1418_ = v_a_1279_;
v___y_1419_ = v_a_1280_;
v___y_1420_ = v_a_1281_;
v___y_1421_ = v_a_1282_;
v___y_1422_ = v_a_1283_;
v___y_1423_ = v_a_1284_;
v___y_1424_ = v_a_1285_;
v___y_1425_ = v_a_1286_;
goto v___jp_1415_;
}
else
{
lean_object* v_inheritedTraceOptions_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_inheritedTraceOptions_1456_ = lean_ctor_get(v_toCold_1453_, 11);
v___x_1457_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1458_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__2, &l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
v___x_1459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1456_, v_options_1454_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_del_object(v___x_1413_);
v___y_1416_ = v_a_1277_;
v___y_1417_ = v_a_1278_;
v___y_1418_ = v_a_1279_;
v___y_1419_ = v_a_1280_;
v___y_1420_ = v_a_1281_;
v___y_1421_ = v_a_1282_;
v___y_1422_ = v_a_1283_;
v___y_1423_ = v_a_1284_;
v___y_1424_ = v_a_1285_;
v___y_1425_ = v_a_1286_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_Grind_updateLastTag(v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1460_, 1);
lean_inc_ref(v_e_1276_);
v___x_1461_ = l_Lean_MessageData_ofExpr(v_e_1276_);
v___x_1462_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__4, &l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 7);
lean_ctor_set(v___x_1413_, 1, v___x_1462_);
lean_ctor_set(v___x_1413_, 0, v___x_1461_);
v___x_1464_ = v___x_1413_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_inc(v_fst_1410_);
v___x_1465_ = l_Lean_MessageData_ofExpr(v_fst_1410_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v___x_1457_, v___x_1466_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v___y_1416_ = v_a_1277_;
v___y_1417_ = v_a_1278_;
v___y_1418_ = v_a_1279_;
v___y_1419_ = v_a_1280_;
v___y_1420_ = v_a_1281_;
v___y_1421_ = v_a_1282_;
v___y_1422_ = v_a_1283_;
v___y_1423_ = v_a_1284_;
v___y_1424_ = v_a_1285_;
v___y_1425_ = v_a_1286_;
goto v___jp_1415_;
}
else
{
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref_known(v_e_1276_, 3);
return v___x_1467_;
}
}
}
else
{
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref_known(v_e_1276_, 3);
return v___x_1460_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1426_; 
lean_inc_ref(v_e_1276_);
v___x_1426_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1276_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
lean_inc_ref(v_e_1276_);
v___x_1428_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1276_, v_a_1427_);
v___x_1429_ = l_Lean_Expr_app___override(v_snd_1411_, v___x_1428_);
v___x_1430_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1276_, v___y_1416_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
lean_inc_ref(v_e_1276_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 4);
lean_ctor_set(v___x_1408_, 0, v_e_1276_);
v___x_1433_ = v___x_1408_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_e_1276_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(1);
v___x_1435_ = l_Lean_Meta_Grind_addNewRawFact___redArg(v___x_1429_, v_fst_1410_, v_a_1431_, v___x_1433_, v___x_1434_, v___y_1416_, v___y_1418_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v___y_1296_ = v___y_1416_;
v___y_1297_ = v___y_1417_;
v___y_1298_ = v___y_1418_;
v___y_1299_ = v___y_1419_;
v___y_1300_ = v___y_1420_;
v___y_1301_ = v___y_1421_;
v___y_1302_ = v___y_1422_;
v___y_1303_ = v___y_1423_;
v___y_1304_ = v___y_1424_;
v___y_1305_ = v___y_1425_;
goto v___jp_1295_;
}
else
{
lean_dec_ref_known(v_e_1276_, 3);
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___x_1429_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1437_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1430_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1430_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_snd_1411_);
lean_dec(v_fst_1410_);
lean_del_object(v___x_1408_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1445_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1426_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1426_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1405_);
v___y_1296_ = v_a_1277_;
v___y_1297_ = v_a_1278_;
v___y_1298_ = v_a_1279_;
v___y_1299_ = v_a_1280_;
v___y_1300_ = v_a_1281_;
v___y_1301_ = v_a_1282_;
v___y_1302_ = v_a_1283_;
v___y_1303_ = v_a_1284_;
v___y_1304_ = v_a_1285_;
v___y_1305_ = v_a_1286_;
goto v___jp_1295_;
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1471_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1404_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1404_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1480_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1394_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1394_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v___x_1488_; 
lean_inc_ref(v_binderType_1292_);
v___x_1488_ = l_Lean_Meta_isProp(v_binderType_1292_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; uint8_t v___x_1535_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1535_ = l_Lean_Expr_hasLooseBVars(v_body_1293_);
if (v___x_1535_ == 0)
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_unbox(v_a_1489_);
lean_dec(v_a_1489_);
if (v___x_1536_ == 0)
{
goto v___jp_1490_;
}
else
{
lean_object* v___x_1537_; 
lean_inc_ref(v_body_1293_);
lean_inc_ref(v_binderType_1292_);
v___x_1537_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_n(v_a_1538_, 2);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__11, &l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
lean_inc_ref(v_body_1293_);
lean_inc_ref_n(v_binderType_1292_, 2);
v___x_1540_ = l_Lean_mkApp3(v___x_1539_, v_binderType_1292_, v_body_1293_, v_a_1538_);
v___x_1541_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_binderType_1292_, v___x_1540_, v_a_1277_, v_a_1279_, v_a_1281_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref_known(v___x_1541_, 1);
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__14, &l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
lean_inc_ref(v_body_1293_);
v___x_1543_ = l_Lean_mkApp3(v___x_1542_, v_binderType_1292_, v_body_1293_, v_a_1538_);
v___x_1544_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_body_1293_, v___x_1543_, v_a_1277_, v_a_1279_, v_a_1281_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1544_;
}
else
{
lean_dec(v_a_1538_);
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
return v___x_1541_;
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
v_a_1545_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1537_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1537_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_dec(v_a_1489_);
goto v___jp_1490_;
}
v___jp_1490_:
{
lean_object* v___x_1491_; 
lean_inc_ref(v_binderType_1292_);
v___x_1491_ = l_Lean_Meta_getLevel(v_binderType_1292_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1492_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
lean_inc_ref(v___x_1495_);
v___x_1496_ = l_Lean_mkConst(v___x_1493_, v___x_1495_);
lean_inc_ref(v_body_1293_);
v___x_1497_ = l_Lean_mkNot(v_body_1293_);
lean_inc_ref_n(v_binderType_1292_, 2);
lean_inc(v_binderName_1291_);
v___x_1498_ = l_Lean_mkLambda(v_binderName_1291_, v_binderInfo_1294_, v_binderType_1292_, v___x_1497_);
v___x_1499_ = l_Lean_mkAppB(v___x_1496_, v_binderType_1292_, v___x_1498_);
lean_inc_ref(v_e_1276_);
v___x_1500_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__8));
v___x_1503_ = l_Lean_mkConst(v___x_1502_, v___x_1495_);
lean_inc_ref(v_body_1293_);
lean_inc_ref_n(v_binderType_1292_, 2);
lean_inc(v_binderName_1291_);
v___x_1504_ = l_Lean_mkLambda(v_binderName_1291_, v_binderInfo_1294_, v_binderType_1292_, v_body_1293_);
v___x_1505_ = l_Lean_mkApp3(v___x_1503_, v_binderType_1292_, v___x_1504_, v_a_1501_);
v___x_1506_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_e_1276_);
v___x_1509_ = lean_box(1);
v___x_1510_ = l_Lean_Meta_Grind_addNewRawFact___redArg(v___x_1505_, v___x_1499_, v_a_1507_, v___x_1508_, v___x_1509_, v_a_1277_, v_a_1279_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
return v___x_1510_;
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v___x_1505_);
lean_dec_ref(v___x_1499_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1511_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1506_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1506_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1499_);
lean_dec_ref_known(v___x_1495_, 2);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1519_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1500_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1500_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1527_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1491_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1491_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1553_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1488_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1488_);
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
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1561_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1391_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1391_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
v___jp_1295_:
{
uint8_t v___x_1306_; 
v___x_1306_ = l_Lean_Expr_hasLooseBVars(v_body_1293_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_inc_ref(v_body_1293_);
lean_inc_ref(v_binderType_1292_);
v___x_1307_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_1293_, v___y_1296_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1362_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1362_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1362_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_unbox(v_a_1308_);
lean_dec(v_a_1308_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
v___x_1313_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1315_ = v___x_1310_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
else
{
lean_object* v___x_1317_; 
lean_del_object(v___x_1310_);
lean_inc_ref(v_body_1293_);
v___x_1317_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_1293_, v___y_1296_, v___y_1300_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; uint8_t v___x_1319_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_unbox(v_a_1318_);
lean_dec(v_a_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
goto v___jp_1288_;
}
else
{
lean_object* v___x_1320_; 
lean_inc_ref(v_binderType_1292_);
v___x_1320_ = l_Lean_Meta_isProp(v_binderType_1292_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; uint8_t v___x_1322_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
goto v___jp_1288_;
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1276_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
lean_inc_ref(v_body_1293_);
v___x_1325_ = l_Lean_Meta_Grind_mkEqFalseProof(v_body_1293_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_binderType_1292_);
v___x_1328_ = l_Lean_mkApp4(v___x_1327_, v_binderType_1292_, v_body_1293_, v_a_1324_, v_a_1326_);
v___x_1329_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_binderType_1292_, v___x_1328_, v___y_1296_, v___y_1298_, v___y_1300_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1329_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1324_);
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
v_a_1330_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1325_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1325_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
v_a_1338_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1323_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1323_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1346_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1320_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1320_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1354_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1317_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1317_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_binderType_1292_);
lean_dec_ref_known(v_e_1276_, 3);
v_a_1363_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1307_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1307_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v___x_1371_; 
lean_inc_ref(v_binderType_1292_);
v___x_1371_ = l_Lean_Meta_isProp(v_binderType_1292_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1382_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1382_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1382_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_unbox(v_a_1372_);
lean_dec(v_a_1372_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_del_object(v___x_1374_);
v___x_1377_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1276_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref_known(v_e_1276_, 3);
v___x_1378_ = lean_box(0);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1378_);
v___x_1380_ = v___x_1374_;
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
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref_known(v_e_1276_, 3);
v_a_1383_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1371_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1371_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
lean_dec_ref(v_e_1276_);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
v___jp_1288_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_box(0);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* v_e_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_Grind_propagateForallPropDown(v_e_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec(v_a_1572_);
return v_res_1583_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1589_ = l_Lean_mkConst(v___x_1588_, v___x_1587_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = l_Lean_Expr_bvar___override(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* v_e_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1613_; 
lean_inc_ref(v_e_1598_);
v___x_1613_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1598_, v_a_1599_, v_a_1603_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1668_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1668_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1668_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v_e_1598_);
v___x_1619_ = lean_box(0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1619_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
else
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
lean_del_object(v___x_1616_);
v___x_1623_ = l_Lean_Expr_cleanupAnnotations(v_e_1598_);
v___x_1624_ = l_Lean_Expr_isApp(v___x_1623_);
if (v___x_1624_ == 0)
{
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_e_1598_);
goto v___jp_1610_;
}
else
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1623_);
v___x_1626_ = l_Lean_Expr_isApp(v___x_1625_);
if (v___x_1626_ == 0)
{
lean_dec_ref(v___x_1625_);
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_e_1598_);
goto v___jp_1610_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1627_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1625_);
v___x_1628_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1629_ = l_Lean_Expr_isConstOf(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_dec_ref(v___x_1627_);
lean_dec_ref(v___x_1625_);
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_e_1598_);
goto v___jp_1610_;
}
else
{
lean_object* v_arg_1630_; lean_object* v_arg_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_arg_1630_ = lean_ctor_get(v___x_1623_, 1);
lean_inc_ref_n(v_arg_1630_, 2);
lean_dec_ref(v___x_1623_);
v_arg_1631_ = lean_ctor_get(v___x_1625_, 1);
lean_inc_ref_n(v_arg_1631_, 2);
lean_dec_ref(v___x_1625_);
v___x_1632_ = l_Lean_Expr_constLevels_x21(v___x_1627_);
lean_dec_ref(v___x_1627_);
v___x_1633_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
v___x_1634_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
v___x_1635_ = l_Lean_Expr_app___override(v_arg_1630_, v___x_1634_);
v___x_1636_ = l_Lean_Expr_headBeta(v___x_1635_);
v___x_1637_ = l_Lean_Expr_app___override(v___x_1633_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
v___x_1639_ = 0;
v___x_1640_ = l_Lean_mkForall(v___x_1638_, v___x_1639_, v_arg_1631_, v___x_1637_);
lean_inc_ref(v_e_1598_);
v___x_1641_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
v___x_1644_ = l_Lean_mkConst(v___x_1643_, v___x_1632_);
lean_inc_ref(v_e_1598_);
v___x_1645_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1598_, v_a_1642_);
v___x_1646_ = l_Lean_mkApp3(v___x_1644_, v_arg_1631_, v_arg_1630_, v___x_1645_);
v___x_1647_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1598_, v_a_1599_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_e_1598_);
v___x_1650_ = lean_box(1);
v___x_1651_ = l_Lean_Meta_Grind_addNewRawFact___redArg(v___x_1646_, v___x_1640_, v_a_1648_, v___x_1649_, v___x_1650_, v_a_1599_, v_a_1601_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1651_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v___x_1640_);
lean_dec_ref(v_e_1598_);
v_a_1652_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1647_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v___x_1640_);
lean_dec(v___x_1632_);
lean_dec_ref(v_arg_1631_);
lean_dec_ref(v_arg_1630_);
lean_dec_ref(v_e_1598_);
v_a_1660_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1641_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1641_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
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
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v_e_1598_);
v_a_1669_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1613_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1613_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
v___jp_1610_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* v_e_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Meta_Grind_propagateExistsDown(v_e_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
v___x_1693_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1691_, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9____boxed(lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
return v_res_1695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_1704_ = l_Lean_mkConst(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* v_e_1705_){
_start:
{
if (lean_obj_tag(v_e_1705_) == 7)
{
lean_object* v_binderName_1706_; lean_object* v_binderType_1707_; lean_object* v_body_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_binderName_1706_ = lean_ctor_get(v_e_1705_, 0);
v_binderType_1707_ = lean_ctor_get(v_e_1705_, 1);
v_body_1708_ = lean_ctor_get(v_e_1705_, 2);
lean_inc_ref(v_body_1708_);
lean_inc_ref(v_binderType_1707_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_binderType_1707_);
lean_ctor_set(v___x_1709_, 1, v_body_1708_);
lean_inc(v_binderName_1706_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_binderName_1706_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1713_ = lean_unsigned_to_nat(1u);
v___x_1714_ = l_Lean_Expr_isAppOfArity(v_e_1705_, v___x_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
v___x_1717_ = l_Lean_Expr_appArg_x21(v_e_1705_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1716_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* v_e_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_e_1722_);
lean_dec_ref(v_e_1722_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* v_fst_1724_, lean_object* v_a_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_expr_instantiate1(v_fst_1724_, v_a_1725_);
v___x_1735_ = l_Lean_Meta_getLevel(v___x_1734_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* v_fst_1736_, lean_object* v_a_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_Grind_simpForall___lam__0(v_fst_1736_, v_a_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v_a_1737_);
lean_dec_ref(v_fst_1736_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
lean_inc(v___y_1753_);
lean_inc_ref(v___y_1752_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
lean_inc(v___y_1748_);
v___x_1757_ = lean_apply_9(v_k_1747_, v_b_1751_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, lean_box(0));
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v_b_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v_b_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* v_name_1769_, uint8_t v_bi_1770_, lean_object* v_type_1771_, lean_object* v_k_1772_, uint8_t v_kind_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___f_1782_; lean_object* v___x_1783_; 
lean_inc(v___y_1776_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1774_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1782_, 0, v_k_1772_);
lean_closure_set(v___f_1782_, 1, v___y_1774_);
lean_closure_set(v___f_1782_, 2, v___y_1775_);
lean_closure_set(v___f_1782_, 3, v___y_1776_);
v___x_1783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1769_, v_bi_1770_, v_type_1771_, v___f_1782_, v_kind_1773_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
return v___x_1783_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_1792_, lean_object* v_bi_1793_, lean_object* v_type_1794_, lean_object* v_k_1795_, lean_object* v_kind_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v_bi_boxed_1805_; uint8_t v_kind_boxed_1806_; lean_object* v_res_1807_; 
v_bi_boxed_1805_ = lean_unbox(v_bi_1793_);
v_kind_boxed_1806_ = lean_unbox(v_kind_1796_);
v_res_1807_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1792_, v_bi_boxed_1805_, v_type_1794_, v_k_1795_, v_kind_boxed_1806_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* v_name_1808_, lean_object* v_type_1809_, lean_object* v_k_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = 0;
v___x_1820_ = 0;
v___x_1821_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1808_, v___x_1819_, v_type_1809_, v_k_1810_, v___x_1820_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* v_name_1822_, lean_object* v_type_1823_, lean_object* v_k_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_1822_, v_type_1823_, v_k_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__9(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_1854_ = l_Lean_mkConst(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__12(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__11));
v___x_1862_ = l_Lean_mkConst(v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__17(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__16));
v___x_1873_ = l_Lean_mkConst(v___x_1872_, v___x_1871_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__20(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__19));
v___x_1881_ = l_Lean_mkConst(v___x_1880_, v___x_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__23(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__22));
v___x_1889_ = l_Lean_mkConst(v___x_1888_, v___x_1887_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__26(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__25));
v___x_1896_ = l_Lean_mkConst(v___x_1895_, v___x_1894_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__29(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__28));
v___x_1904_ = l_Lean_mkConst(v___x_1903_, v___x_1902_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = l_Lean_Level_ofNat(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__31(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
v___x_1908_ = l_Lean_mkSort(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__34(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__33));
v___x_1914_ = l_Lean_mkConst(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* v_e_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; 
if (lean_obj_tag(v_e_1915_) == 7)
{
lean_object* v_binderName_1966_; lean_object* v_binderType_1967_; lean_object* v_body_1968_; uint8_t v_binderInfo_1969_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; uint8_t v___x_2135_; 
v_binderName_1966_ = lean_ctor_get(v_e_1915_, 0);
v_binderType_1967_ = lean_ctor_get(v_e_1915_, 1);
v_body_1968_ = lean_ctor_get(v_e_1915_, 2);
v_binderInfo_1969_ = lean_ctor_get_uint8(v_e_1915_, sizeof(void*)*3 + 8);
v___x_2135_ = l_Lean_Expr_hasLooseBVars(v_body_1968_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = 1;
lean_inc_ref(v_binderType_1967_);
v___x_2137_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1967_, v_a_1920_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_Expr_cleanupAnnotations(v_a_2138_);
lean_dec(v_a_2138_);
v___x_2140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2141_ = l_Lean_Expr_isConstOf(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2143_ = l_Lean_Expr_isConstOf(v___x_2139_, v___x_2142_);
lean_dec_ref(v___x_2139_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_inc_ref(v_body_1968_);
v___x_2144_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_1968_, v_a_1920_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Expr_cleanupAnnotations(v_a_2145_);
lean_dec(v_a_2145_);
v___x_2147_ = l_Lean_Expr_isConstOf(v___x_2146_, v___x_2140_);
if (v___x_2147_ == 0)
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Lean_Expr_isConstOf(v___x_2146_, v___x_2142_);
lean_dec_ref(v___x_2146_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_inc_ref(v_binderType_1967_);
v___x_2149_ = l_Lean_Meta_isProp(v_binderType_1967_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; uint8_t v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = lean_unbox(v_a_2150_);
lean_dec(v_a_2150_);
if (v___x_2151_ == 0)
{
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2152_; 
lean_inc_ref(v_body_1968_);
lean_inc_ref(v_binderType_1967_);
v___x_2152_ = l_Lean_Meta_isExprDefEq(v_binderType_1967_, v_body_1968_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2167_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2167_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2167_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_unbox(v_a_2153_);
lean_dec(v_a_2153_);
if (v___x_2157_ == 0)
{
lean_del_object(v___x_2155_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_inc_ref(v_binderType_1967_);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2158_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2159_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__12, &l_Lean_Meta_Grind_simpForall___closed__12_once, _init_l_Lean_Meta_Grind_simpForall___closed__12);
v___x_2160_ = l_Lean_Expr_app___override(v___x_2159_, v_binderType_1967_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2158_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*2, v___x_2136_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2163_);
v___x_2165_ = v___x_2155_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2168_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2152_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2152_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2176_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2149_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2149_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; 
lean_inc_ref_n(v_binderType_1967_, 2);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2184_ = l_Lean_Meta_getLevel(v_binderType_1967_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2201_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2201_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2201_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2191_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__14));
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2185_);
lean_ctor_set(v___x_2192_, 1, v___x_2189_);
v___x_2193_ = l_Lean_mkConst(v___x_2191_, v___x_2192_);
v___x_2194_ = l_Lean_Expr_app___override(v___x_2193_, v_binderType_1967_);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2196_, 0, v___x_2190_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
lean_ctor_set_uint8(v___x_2196_, sizeof(void*)*2, v___x_2136_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2197_);
v___x_2199_ = v___x_2187_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_binderType_1967_);
v_a_2202_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2184_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2184_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v___x_2210_; 
lean_dec_ref(v___x_2146_);
lean_inc_ref(v_binderType_1967_);
v___x_2210_ = l_Lean_Meta_isProp(v_binderType_1967_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2225_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2225_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2225_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint8_t v___x_2215_; 
v___x_2215_ = lean_unbox(v_a_2211_);
lean_dec(v_a_2211_);
if (v___x_2215_ == 0)
{
lean_del_object(v___x_2213_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
lean_inc_ref_n(v_binderType_1967_, 2);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2216_ = l_Lean_mkNot(v_binderType_1967_);
v___x_2217_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__17, &l_Lean_Meta_Grind_simpForall___closed__17_once, _init_l_Lean_Meta_Grind_simpForall___closed__17);
v___x_2218_ = l_Lean_Expr_app___override(v___x_2217_, v_binderType_1967_);
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2220_, 0, v___x_2216_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*2, v___x_2136_);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2221_);
v___x_2223_ = v___x_2213_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2226_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2210_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2210_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2234_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2144_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2144_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v___x_2242_; 
lean_inc_ref(v_body_1968_);
v___x_2242_ = l_Lean_Meta_isProp(v_body_1968_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2256_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_unbox(v_a_2243_);
lean_dec(v_a_2243_);
if (v___x_2247_ == 0)
{
lean_del_object(v___x_2245_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_inc_ref_n(v_body_1968_, 2);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2248_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__20, &l_Lean_Meta_Grind_simpForall___closed__20_once, _init_l_Lean_Meta_Grind_simpForall___closed__20);
v___x_2249_ = l_Lean_Expr_app___override(v___x_2248_, v_body_1968_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2251_, 0, v_body_1968_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*2, v___x_2136_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2252_);
v___x_2254_ = v___x_2245_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2257_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2242_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2242_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v___x_2265_; 
lean_dec_ref(v___x_2139_);
lean_inc_ref(v_body_1968_);
v___x_2265_ = l_Lean_Meta_isProp(v_body_1968_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2280_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2280_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2280_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_unbox(v_a_2266_);
lean_dec(v_a_2266_);
if (v___x_2270_ == 0)
{
lean_del_object(v___x_2268_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_inc_ref(v_body_1968_);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2271_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2272_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__23, &l_Lean_Meta_Grind_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_simpForall___closed__23);
v___x_2273_ = l_Lean_Expr_app___override(v___x_2272_, v_body_1968_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2275_, 0, v___x_2271_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*2, v___x_2136_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2276_);
v___x_2278_ = v___x_2268_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2281_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2265_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2265_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2289_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2137_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2137_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; 
lean_inc_ref(v_binderType_1967_);
v___x_2297_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1967_, v_a_1920_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_Expr_cleanupAnnotations(v_a_2298_);
lean_dec(v_a_2298_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2301_ = l_Lean_Expr_isConstOf(v___x_2299_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2303_ = l_Lean_Expr_isConstOf(v___x_2299_, v___x_2302_);
lean_dec_ref(v___x_2299_);
if (v___x_2303_ == 0)
{
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__26, &l_Lean_Meta_Grind_simpForall___closed__26_once, _init_l_Lean_Meta_Grind_simpForall___closed__26);
v___x_2305_ = lean_expr_instantiate1(v_body_1968_, v___x_2304_);
lean_inc_ref(v___x_2305_);
v___x_2306_ = l_Lean_Meta_isProp(v___x_2305_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2321_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2321_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2321_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
uint8_t v___x_2311_; 
v___x_2311_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
if (v___x_2311_ == 0)
{
lean_del_object(v___x_2309_);
lean_dec_ref(v___x_2305_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_inc_ref(v_body_1968_);
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2312_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_body_1968_);
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__29, &l_Lean_Meta_Grind_simpForall___closed__29_once, _init_l_Lean_Meta_Grind_simpForall___closed__29);
v___x_2314_ = l_Lean_Expr_app___override(v___x_2313_, v___x_2312_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2316_, 0, v___x_2305_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*2, v___x_2135_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2317_);
v___x_2319_ = v___x_2309_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v___x_2305_);
lean_dec_ref_known(v_e_1915_, 3);
v_a_2322_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2306_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2306_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref(v___x_2299_);
lean_inc_ref(v_body_1968_);
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
v___x_2330_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_body_1968_);
lean_inc(v_a_1922_);
lean_inc_ref(v_a_1921_);
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc_ref(v___x_2330_);
v___x_2331_ = lean_infer_type(v___x_2330_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__31, &l_Lean_Meta_Grind_simpForall___closed__31_once, _init_l_Lean_Meta_Grind_simpForall___closed__31);
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
v___x_2334_ = l_Lean_mkForall(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v___x_2333_);
v___x_2335_ = l_Lean_Meta_isExprDefEq(v_a_2332_, v___x_2334_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2350_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_unbox(v_a_2336_);
lean_dec(v_a_2336_);
if (v___x_2340_ == 0)
{
lean_del_object(v___x_2338_);
lean_dec_ref(v___x_2330_);
v___y_1971_ = v_a_1916_;
v___y_1972_ = v_a_1917_;
v___y_1973_ = v_a_1918_;
v___y_1974_ = v_a_1919_;
v___y_1975_ = v_a_1920_;
v___y_1976_ = v_a_1921_;
v___y_1977_ = v_a_1922_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
lean_dec_ref_known(v_e_1915_, 3);
v___x_2341_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2342_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__34, &l_Lean_Meta_Grind_simpForall___closed__34_once, _init_l_Lean_Meta_Grind_simpForall___closed__34);
v___x_2343_ = l_Lean_Expr_app___override(v___x_2342_, v___x_2330_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2345_, 0, v___x_2341_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*2, v___x_2135_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2346_);
v___x_2348_ = v___x_2338_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref_known(v_e_1915_, 3);
v_a_2351_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2335_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2335_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref_known(v_e_1915_, 3);
v_a_2359_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2331_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2331_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref_known(v_e_1915_, 3);
v_a_2367_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2297_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2297_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
v___jp_1970_:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Lean_Expr_isApp(v_body_1968_);
if (v___x_1978_ == 0)
{
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
v___y_1927_ = v___y_1976_;
v___y_1928_ = v___y_1977_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = l_Lean_Expr_getAppNumArgs(v_body_1968_);
v___x_1980_ = lean_unsigned_to_nat(2u);
v___x_1981_ = lean_nat_dec_eq(v___x_1979_, v___x_1980_);
lean_dec(v___x_1979_);
if (v___x_1981_ == 0)
{
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
v___y_1927_ = v___y_1976_;
v___y_1928_ = v___y_1977_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l_Lean_Expr_appFn_x21(v_body_1968_);
v___x_1983_ = l_Lean_Expr_appFn_x21(v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 4)
{
lean_object* v_declName_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_declName_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_declName_1984_);
lean_dec_ref_known(v___x_1983_, 2);
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_1986_ = lean_name_eq(v_declName_1984_, v___x_1985_);
lean_dec(v_declName_1984_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v___x_1982_);
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
v___y_1927_ = v___y_1976_;
v___y_1928_ = v___y_1977_;
goto v___jp_1924_;
}
else
{
lean_object* v_pRaw_1987_; lean_object* v_pRaw_1988_; lean_object* v___x_1989_; 
v_pRaw_1987_ = l_Lean_Expr_appArg_x21(v___x_1982_);
lean_dec_ref(v___x_1982_);
v_pRaw_1988_ = l_Lean_Expr_appArg_x21(v_body_1968_);
v___x_1989_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1987_);
if (lean_obj_tag(v___x_1989_) == 1)
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2060_; 
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
lean_dec_ref(v_pRaw_1987_);
lean_dec_ref_known(v_e_1915_, 3);
v_val_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2060_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2060_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_snd_1994_; lean_object* v_fst_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2059_; 
v_snd_1994_ = lean_ctor_get(v_val_1990_, 1);
v_fst_1995_ = lean_ctor_get(v_val_1990_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_val_1990_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_1997_ = v_val_1990_;
v_isShared_1998_ = v_isSharedCheck_2059_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1995_);
lean_dec(v_val_1990_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2059_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_fst_1999_; lean_object* v_snd_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2058_; 
v_fst_1999_ = lean_ctor_get(v_snd_1994_, 0);
v_snd_2000_ = lean_ctor_get(v_snd_1994_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_snd_1994_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2002_ = v_snd_1994_;
v_isShared_2003_ = v_isSharedCheck_2058_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_snd_2000_);
lean_inc(v_fst_1999_);
lean_dec(v_snd_1994_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2058_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___f_2004_; lean_object* v_p_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_q_2008_; lean_object* v_00_u03b2_2009_; lean_object* v___x_2010_; 
lean_inc_n(v_fst_1999_, 3);
v___f_2004_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2004_, 0, v_fst_1999_);
lean_inc_ref(v_pRaw_1988_);
lean_inc_ref_n(v_binderType_1967_, 4);
lean_inc_n(v_binderName_1966_, 3);
v_p_2005_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_pRaw_1988_);
v___x_2006_ = 0;
lean_inc(v_snd_2000_);
lean_inc(v_fst_1995_);
v___x_2007_ = l_Lean_mkLambda(v_fst_1995_, v___x_2006_, v_fst_1999_, v_snd_2000_);
v_q_2008_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v___x_2007_);
v_00_u03b2_2009_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_fst_1999_);
v___x_2010_ = l_Lean_Meta_getLevel(v_binderType_1967_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
v___x_2012_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1966_, v_binderType_1967_, v___f_2004_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2041_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2041_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_expr_lift_loose_bvars(v_pRaw_1988_, v___x_2017_, v___x_2018_);
lean_dec_ref(v_pRaw_1988_);
v___x_2020_ = l_Lean_mkOr(v_snd_2000_, v___x_2019_);
v___x_2021_ = l_Lean_mkForall(v_fst_1995_, v___x_2006_, v_fst_1999_, v___x_2020_);
lean_inc_ref(v_binderType_1967_);
v___x_2022_ = l_Lean_mkForall(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v___x_2021_);
v___x_2023_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_2024_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 1, v___x_2024_);
lean_ctor_set(v___x_2002_, 0, v_a_2013_);
v___x_2026_ = v___x_2002_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2013_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 1, v___x_2026_);
lean_ctor_set(v___x_1997_, 0, v_a_2011_);
v___x_2028_ = v___x_1997_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2011_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = l_Lean_mkConst(v___x_2023_, v___x_2028_);
v___x_2030_ = l_Lean_mkApp4(v___x_2029_, v_binderType_1967_, v_00_u03b2_2009_, v_p_2005_, v_q_2008_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2030_);
v___x_2032_ = v___x_1992_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2033_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2033_, 0, v___x_2022_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2, v___x_1978_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2034_);
v___x_2036_ = v___x_2015_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_a_2011_);
lean_dec_ref(v_00_u03b2_2009_);
lean_dec_ref(v_q_2008_);
lean_dec_ref(v_p_2005_);
lean_del_object(v___x_2002_);
lean_dec(v_snd_2000_);
lean_dec(v_fst_1999_);
lean_del_object(v___x_1997_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_pRaw_1988_);
lean_dec_ref(v_binderType_1967_);
lean_dec(v_binderName_1966_);
v_a_2042_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2012_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2012_);
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
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_00_u03b2_2009_);
lean_dec_ref(v_q_2008_);
lean_dec_ref(v_p_2005_);
lean_dec_ref(v___f_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_snd_2000_);
lean_dec(v_fst_1999_);
lean_del_object(v___x_1997_);
lean_dec(v_fst_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_pRaw_1988_);
lean_dec_ref(v_binderType_1967_);
lean_dec(v_binderName_1966_);
v_a_2050_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2010_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2010_);
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
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v___x_1989_);
v___x_2061_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1988_);
lean_dec_ref(v_pRaw_1988_);
if (lean_obj_tag(v___x_2061_) == 1)
{
lean_object* v_val_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2132_; 
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
lean_dec_ref_known(v_e_1915_, 3);
v_val_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2132_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_val_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2132_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_snd_2066_; lean_object* v_fst_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2131_; 
v_snd_2066_ = lean_ctor_get(v_val_2062_, 1);
v_fst_2067_ = lean_ctor_get(v_val_2062_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_val_2062_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2069_ = v_val_2062_;
v_isShared_2070_ = v_isSharedCheck_2131_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_snd_2066_);
lean_inc(v_fst_2067_);
lean_dec(v_val_2062_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2131_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2130_; 
v_fst_2071_ = lean_ctor_get(v_snd_2066_, 0);
v_snd_2072_ = lean_ctor_get(v_snd_2066_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_snd_2066_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2074_ = v_snd_2066_;
v_isShared_2075_ = v_isSharedCheck_2130_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_snd_2072_);
lean_inc(v_fst_2071_);
lean_dec(v_snd_2066_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2130_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___f_2076_; lean_object* v_p_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v_q_2080_; lean_object* v_00_u03b2_2081_; lean_object* v___x_2082_; 
lean_inc_n(v_fst_2071_, 3);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2076_, 0, v_fst_2071_);
lean_inc_ref(v_pRaw_1987_);
lean_inc_ref_n(v_binderType_1967_, 4);
lean_inc_n(v_binderName_1966_, 3);
v_p_2077_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_pRaw_1987_);
v___x_2078_ = 0;
lean_inc(v_snd_2072_);
lean_inc(v_fst_2067_);
v___x_2079_ = l_Lean_mkLambda(v_fst_2067_, v___x_2078_, v_fst_2071_, v_snd_2072_);
v_q_2080_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v___x_2079_);
v_00_u03b2_2081_ = l_Lean_mkLambda(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v_fst_2071_);
v___x_2082_ = l_Lean_Meta_getLevel(v_binderType_1967_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
lean_inc_ref(v_binderType_1967_);
lean_inc(v_binderName_1966_);
v___x_2084_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1966_, v_binderType_1967_, v___f_2076_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2113_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2113_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2113_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_expr_lift_loose_bvars(v_pRaw_1987_, v___x_2089_, v___x_2090_);
lean_dec_ref(v_pRaw_1987_);
v___x_2092_ = l_Lean_mkOr(v___x_2091_, v_snd_2072_);
v___x_2093_ = l_Lean_mkForall(v_fst_2067_, v___x_2078_, v_fst_2071_, v___x_2092_);
lean_inc_ref(v_binderType_1967_);
v___x_2094_ = l_Lean_mkForall(v_binderName_1966_, v_binderInfo_1969_, v_binderType_1967_, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
v___x_2096_ = lean_box(0);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 1);
lean_ctor_set(v___x_2074_, 1, v___x_2096_);
lean_ctor_set(v___x_2074_, 0, v_a_2085_);
v___x_2098_ = v___x_2074_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2085_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 1);
lean_ctor_set(v___x_2069_, 1, v___x_2098_);
lean_ctor_set(v___x_2069_, 0, v_a_2083_);
v___x_2100_ = v___x_2069_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2083_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = l_Lean_mkConst(v___x_2095_, v___x_2100_);
v___x_2102_ = l_Lean_mkApp4(v___x_2101_, v_binderType_1967_, v_00_u03b2_2081_, v_p_2077_, v_q_2080_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2102_);
v___x_2104_ = v___x_2064_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2105_, 0, v___x_2094_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*2, v___x_1978_);
v___x_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2106_);
v___x_2108_ = v___x_2087_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2083_);
lean_dec_ref(v_00_u03b2_2081_);
lean_dec_ref(v_q_2080_);
lean_dec_ref(v_p_2077_);
lean_del_object(v___x_2074_);
lean_dec(v_snd_2072_);
lean_dec(v_fst_2071_);
lean_del_object(v___x_2069_);
lean_dec(v_fst_2067_);
lean_del_object(v___x_2064_);
lean_dec_ref(v_pRaw_1987_);
lean_dec_ref(v_binderType_1967_);
lean_dec(v_binderName_1966_);
v_a_2114_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2084_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2084_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_00_u03b2_2081_);
lean_dec_ref(v_q_2080_);
lean_dec_ref(v_p_2077_);
lean_dec_ref(v___f_2076_);
lean_del_object(v___x_2074_);
lean_dec(v_snd_2072_);
lean_dec(v_fst_2071_);
lean_del_object(v___x_2069_);
lean_dec(v_fst_2067_);
lean_del_object(v___x_2064_);
lean_dec_ref(v_pRaw_1987_);
lean_dec_ref(v_binderType_1967_);
lean_dec(v_binderName_1966_);
v_a_2122_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2082_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2082_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2061_);
lean_dec_ref(v_pRaw_1987_);
v___y_1925_ = v___y_1974_;
v___y_1926_ = v___y_1975_;
v___y_1927_ = v___y_1976_;
v___y_1928_ = v___y_1977_;
goto v___jp_1924_;
}
}
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref(v___x_1983_);
lean_dec_ref(v___x_1982_);
lean_dec_ref_known(v_e_1915_, 3);
v___x_2133_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec_ref(v_e_1915_);
v___x_2375_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
v___jp_1924_:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_1915_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1957_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1957_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1957_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
if (lean_obj_tag(v_a_1930_) == 1)
{
lean_object* v_val_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1952_; 
v_val_1934_ = lean_ctor_get(v_a_1930_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_a_1930_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1936_ = v_a_1930_;
v_isShared_1937_ = v_isSharedCheck_1952_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_val_1934_);
lean_dec(v_a_1930_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1952_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_snd_1938_; lean_object* v_fst_1939_; lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v_snd_1938_ = lean_ctor_get(v_val_1934_, 1);
lean_inc(v_snd_1938_);
v_fst_1939_ = lean_ctor_get(v_val_1934_, 0);
lean_inc(v_fst_1939_);
lean_dec(v_val_1934_);
v_fst_1940_ = lean_ctor_get(v_snd_1938_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_snd_1938_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_snd_1938_);
v___x_1942_ = l_Lean_mkAnd(v_fst_1939_, v_fst_1940_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_snd_1941_);
v___x_1944_ = v___x_1936_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_snd_1941_);
v___x_1944_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1945_ = 1;
v___x_1946_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1946_, 0, v___x_1942_);
lean_ctor_set(v___x_1946_, 1, v___x_1944_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*2, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1947_);
v___x_1949_ = v___x_1932_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_dec(v_a_1930_);
v___x_1953_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1953_);
v___x_1955_ = v___x_1932_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_a_1958_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1929_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1929_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* v_e_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_Grind_simpForall(v_e_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* v_00_u03b1_2387_, lean_object* v_name_2388_, uint8_t v_bi_2389_, lean_object* v_type_2390_, lean_object* v_k_2391_, uint8_t v_kind_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_2388_, v_bi_2389_, v_type_2390_, v_k_2391_, v_kind_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2402_, lean_object* v_name_2403_, lean_object* v_bi_2404_, lean_object* v_type_2405_, lean_object* v_k_2406_, lean_object* v_kind_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v_bi_boxed_2416_; uint8_t v_kind_boxed_2417_; lean_object* v_res_2418_; 
v_bi_boxed_2416_ = lean_unbox(v_bi_2404_);
v_kind_boxed_2417_ = lean_unbox(v_kind_2407_);
v_res_2418_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_2402_, v_name_2403_, v_bi_boxed_2416_, v_type_2405_, v_k_2406_, v_kind_boxed_2417_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* v_00_u03b1_2419_, lean_object* v_name_2420_, lean_object* v_type_2421_, lean_object* v_k_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_2420_, v_type_2421_, v_k_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_name_2433_, lean_object* v_type_2434_, lean_object* v_k_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(v_00_u03b1_2432_, v_name_2433_, v_type_2434_, v_k_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_));
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_));
v___x_2461_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
v___x_2462_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2459_, v___x_2460_, v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12____boxed(lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_();
return v_res_2464_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_box(0);
v___x_2479_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
v___x_2480_ = l_Lean_mkConst(v___x_2479_, v___x_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* v_e_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = l_Lean_Expr_cleanupAnnotations(v_e_2499_);
v___x_2512_ = l_Lean_Expr_isApp(v___x_2511_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v___x_2511_);
goto v___jp_2508_;
}
else
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2511_);
v___x_2514_ = l_Lean_Expr_isApp(v___x_2513_);
if (v___x_2514_ == 0)
{
lean_dec_ref(v___x_2513_);
lean_dec_ref(v___x_2511_);
goto v___jp_2508_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2515_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2513_);
v___x_2516_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2517_ = l_Lean_Expr_isConstOf(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2513_);
lean_dec_ref(v___x_2511_);
goto v___jp_2508_;
}
else
{
lean_object* v_arg_2518_; 
v_arg_2518_ = lean_ctor_get(v___x_2511_, 1);
lean_inc_ref(v_arg_2518_);
lean_dec_ref(v___x_2511_);
if (lean_obj_tag(v_arg_2518_) == 6)
{
lean_object* v_binderName_2519_; lean_object* v_body_2520_; lean_object* v_arg_2521_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; uint8_t v___x_2586_; 
v_binderName_2519_ = lean_ctor_get(v_arg_2518_, 0);
lean_inc(v_binderName_2519_);
v_body_2520_ = lean_ctor_get(v_arg_2518_, 2);
lean_inc_ref(v_body_2520_);
lean_dec_ref_known(v_arg_2518_, 3);
v_arg_2521_ = lean_ctor_get(v___x_2513_, 1);
lean_inc_ref(v_arg_2521_);
lean_dec_ref(v___x_2513_);
v___x_2586_ = l_Lean_Expr_isApp(v_body_2520_);
if (v___x_2586_ == 0)
{
lean_dec(v_binderName_2519_);
v___y_2523_ = v_a_2500_;
v___y_2524_ = v_a_2501_;
v___y_2525_ = v_a_2502_;
v___y_2526_ = v_a_2503_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = l_Lean_Expr_getAppNumArgs(v_body_2520_);
v___x_2588_ = lean_unsigned_to_nat(2u);
v___x_2589_ = lean_nat_dec_eq(v___x_2587_, v___x_2588_);
lean_dec(v___x_2587_);
if (v___x_2589_ == 0)
{
lean_dec(v_binderName_2519_);
v___y_2523_ = v_a_2500_;
v___y_2524_ = v_a_2501_;
v___y_2525_ = v_a_2502_;
v___y_2526_ = v_a_2503_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = l_Lean_Expr_appFn_x21(v_body_2520_);
v___x_2591_ = l_Lean_Expr_appFn_x21(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 4)
{
lean_object* v_declName_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v_declName_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_declName_2592_);
lean_dec_ref_known(v___x_2591_, 2);
v___x_2593_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_2594_ = lean_name_eq(v_declName_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
v___x_2596_ = lean_name_eq(v_declName_2592_, v___x_2595_);
lean_dec(v_declName_2592_);
if (v___x_2596_ == 0)
{
lean_dec_ref(v___x_2590_);
lean_dec(v_binderName_2519_);
v___y_2523_ = v_a_2500_;
v___y_2524_ = v_a_2501_;
v___y_2525_ = v_a_2502_;
v___y_2526_ = v_a_2503_;
goto v___jp_2522_;
}
else
{
lean_object* v_b_2597_; lean_object* v_b_2598_; uint8_t v___x_2599_; 
v_b_2597_ = l_Lean_Expr_appArg_x21(v___x_2590_);
lean_dec_ref(v___x_2590_);
v_b_2598_ = l_Lean_Expr_appArg_x21(v_body_2520_);
v___x_2599_ = l_Lean_Expr_hasLooseBVars(v_b_2597_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; lean_object* v_p_2601_; lean_object* v___x_2602_; lean_object* v_expr_2603_; lean_object* v_u_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v_body_2520_);
v___x_2600_ = 0;
lean_inc_ref_n(v_arg_2521_, 2);
v_p_2601_ = l_Lean_mkLambda(v_binderName_2519_, v___x_2600_, v_arg_2521_, v_b_2598_);
lean_inc_ref(v_p_2601_);
lean_inc_ref(v___x_2515_);
v___x_2602_ = l_Lean_mkAppB(v___x_2515_, v_arg_2521_, v_p_2601_);
lean_inc_ref(v_b_2597_);
v_expr_2603_ = l_Lean_mkAnd(v_b_2597_, v___x_2602_);
v_u_2604_ = l_Lean_Expr_constLevels_x21(v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2605_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
v___x_2606_ = l_Lean_mkConst(v___x_2605_, v_u_2604_);
v___x_2607_ = l_Lean_mkApp3(v___x_2606_, v_arg_2521_, v_p_2601_, v_b_2597_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2609_, 0, v_expr_2603_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*2, v___x_2517_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
else
{
uint8_t v___x_2612_; 
v___x_2612_ = l_Lean_Expr_hasLooseBVars(v_b_2598_);
if (v___x_2612_ == 0)
{
uint8_t v___x_2613_; lean_object* v_p_2614_; lean_object* v___x_2615_; lean_object* v_expr_2616_; lean_object* v_u_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v_body_2520_);
v___x_2613_ = 0;
lean_inc_ref_n(v_arg_2521_, 2);
v_p_2614_ = l_Lean_mkLambda(v_binderName_2519_, v___x_2613_, v_arg_2521_, v_b_2597_);
lean_inc_ref(v_p_2614_);
lean_inc_ref(v___x_2515_);
v___x_2615_ = l_Lean_mkAppB(v___x_2515_, v_arg_2521_, v_p_2614_);
lean_inc_ref(v_b_2598_);
v_expr_2616_ = l_Lean_mkAnd(v___x_2615_, v_b_2598_);
v_u_2617_ = l_Lean_Expr_constLevels_x21(v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2618_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
v___x_2619_ = l_Lean_mkConst(v___x_2618_, v_u_2617_);
v___x_2620_ = l_Lean_mkApp3(v___x_2619_, v_arg_2521_, v_p_2614_, v_b_2598_);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
v___x_2622_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2622_, 0, v_expr_2616_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*2, v___x_2517_);
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
else
{
lean_dec_ref(v_b_2598_);
lean_dec_ref(v_b_2597_);
lean_dec(v_binderName_2519_);
v___y_2523_ = v_a_2500_;
v___y_2524_ = v_a_2501_;
v___y_2525_ = v_a_2502_;
v___y_2526_ = v_a_2503_;
goto v___jp_2522_;
}
}
}
}
else
{
lean_object* v_pRaw_2625_; lean_object* v_qRaw_2626_; uint8_t v___x_2627_; lean_object* v_p_2628_; lean_object* v_q_2629_; lean_object* v_u_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_expr_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec(v_declName_2592_);
v_pRaw_2625_ = l_Lean_Expr_appArg_x21(v___x_2590_);
lean_dec_ref(v___x_2590_);
v_qRaw_2626_ = l_Lean_Expr_appArg_x21(v_body_2520_);
lean_dec_ref(v_body_2520_);
v___x_2627_ = 0;
lean_inc_ref_n(v_arg_2521_, 4);
lean_inc(v_binderName_2519_);
v_p_2628_ = l_Lean_mkLambda(v_binderName_2519_, v___x_2627_, v_arg_2521_, v_pRaw_2625_);
v_q_2629_ = l_Lean_mkLambda(v_binderName_2519_, v___x_2627_, v_arg_2521_, v_qRaw_2626_);
v_u_2630_ = l_Lean_Expr_constLevels_x21(v___x_2515_);
lean_inc_ref(v_p_2628_);
lean_inc_ref(v___x_2515_);
v___x_2631_ = l_Lean_mkAppB(v___x_2515_, v_arg_2521_, v_p_2628_);
lean_inc_ref(v_q_2629_);
v___x_2632_ = l_Lean_mkAppB(v___x_2515_, v_arg_2521_, v_q_2629_);
v_expr_2633_ = l_Lean_mkOr(v___x_2631_, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__14));
v___x_2635_ = l_Lean_mkConst(v___x_2634_, v_u_2630_);
v___x_2636_ = l_Lean_mkApp3(v___x_2635_, v_arg_2521_, v_p_2628_, v_q_2629_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2638_, 0, v_expr_2633_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
lean_ctor_set_uint8(v___x_2638_, sizeof(void*)*2, v___x_2517_);
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref(v___x_2591_);
lean_dec_ref(v___x_2590_);
lean_dec_ref(v_arg_2521_);
lean_dec_ref(v_body_2520_);
lean_dec(v_binderName_2519_);
lean_dec_ref(v___x_2515_);
v___x_2641_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
}
v___jp_2522_:
{
uint8_t v___x_2527_; 
v___x_2527_ = l_Lean_Expr_hasLooseBVars(v_body_2520_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_inc_ref(v_arg_2521_);
v___x_2528_ = l_Lean_Meta_isProp(v_arg_2521_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2577_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2577_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2577_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v___x_2533_; 
v___x_2533_ = lean_unbox(v_a_2529_);
lean_dec(v_a_2529_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_del_object(v___x_2531_);
v___x_2534_ = l_Lean_Expr_constLevels_x21(v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2535_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(v___x_2534_);
v___x_2536_ = l_Lean_mkConst(v___x_2535_, v___x_2534_);
lean_inc_ref(v_arg_2521_);
v___x_2537_ = l_Lean_Expr_app___override(v___x_2536_, v_arg_2521_);
v___x_2538_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2537_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2559_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2559_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2559_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
if (lean_obj_tag(v_a_2539_) == 1)
{
lean_object* v_val_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2558_; 
v_val_2543_ = lean_ctor_get(v_a_2539_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2545_ = v_a_2539_;
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_val_2543_);
lean_dec(v_a_2539_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2558_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2547_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
v___x_2548_ = l_Lean_mkConst(v___x_2547_, v___x_2534_);
lean_inc_ref(v_body_2520_);
v___x_2549_ = l_Lean_mkApp3(v___x_2548_, v_arg_2521_, v_val_2543_, v_body_2520_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2549_);
v___x_2551_ = v___x_2545_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2552_, 0, v_body_2520_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*2, v___x_2517_);
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2553_);
v___x_2555_ = v___x_2541_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_del_object(v___x_2541_);
lean_dec(v_a_2539_);
lean_dec(v___x_2534_);
lean_dec_ref(v_arg_2521_);
lean_dec_ref(v_body_2520_);
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v___x_2534_);
lean_dec_ref(v_arg_2521_);
lean_dec_ref(v_body_2520_);
v_a_2560_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2538_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2538_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
lean_dec_ref(v___x_2515_);
lean_inc_ref(v_body_2520_);
lean_inc_ref(v_arg_2521_);
v___x_2568_ = l_Lean_mkAnd(v_arg_2521_, v_body_2520_);
v___x_2569_ = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
v___x_2570_ = l_Lean_mkAppB(v___x_2569_, v_arg_2521_, v_body_2520_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2572_, 0, v___x_2568_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_ctor_set_uint8(v___x_2572_, sizeof(void*)*2, v___x_2517_);
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2573_);
v___x_2575_ = v___x_2531_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_arg_2521_);
lean_dec_ref(v_body_2520_);
lean_dec_ref(v___x_2515_);
v_a_2578_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2528_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2528_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2521_);
lean_dec_ref(v_body_2520_);
lean_dec_ref(v___x_2515_);
goto v___jp_2505_;
}
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec_ref(v_arg_2518_);
lean_dec_ref(v___x_2515_);
lean_dec_ref(v___x_2513_);
v___x_2643_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
}
}
v___jp_2505_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
v___jp_2508_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* v_e_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec_ref(v_e_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* v_e_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2652_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* v_e_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Meta_Grind_simpExists(v_e_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_e_2662_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2691_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
v___x_2692_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2689_, v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11____boxed(lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* v_s_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_));
v___x_2700_ = 1;
v___x_2701_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2695_, v___x_2699_, v___x_2700_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2704_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2702_, v___x_2703_, v___x_2700_, v_a_2696_, v_a_2697_);
return v___x_2704_;
}
else
{
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* v_s_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Meta_Grind_addForallSimproc(v_s_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
return v_res_2709_;
}
}
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
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
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_200448206____hygCtx___hyg_12_();
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
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
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
