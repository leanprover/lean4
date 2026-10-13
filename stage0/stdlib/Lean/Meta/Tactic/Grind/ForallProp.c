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
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
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
lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_true_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__13_value),LEAN_SCALAR_PTR_LITERAL(23, 129, 235, 110, 107, 55, 234, 42)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__15;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__16_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__18;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__19_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__21;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__22_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__25_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__27;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__28_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__31;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__32;
static const lean_string_object l_Lean_Meta_Grind_simpForall___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpForall___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpForall___closed__33_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_simpForall___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_simpForall___closed__34_value;
static lean_once_cell_t l_Lean_Meta_Grind_simpForall___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__35;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpForall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(207, 161, 230, 164, 57, 132, 181, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12____boxed(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_simpExists___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_simpExists___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_simpExists___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
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
v___x_198_ = lean_unbox(v_a_197_);
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
v___x_98_ = lean_unbox(v_a_97_);
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
v___x_101_ = lean_unbox(v_a_100_);
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
v___x_131_ = lean_unbox(v_a_130_);
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
v___x_160_ = lean_unbox(v_a_159_);
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
lean_object* v___x_270_; lean_object* v_env_271_; uint8_t v___x_272_; lean_object* v_env_273_; lean_object* v___x_274_; lean_object* v_toCold_275_; lean_object* v_mctx_276_; lean_object* v_lctx_277_; lean_object* v_options_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_270_ = lean_st_ref_get(v___y_268_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_env_271_);
lean_dec(v___x_270_);
v___x_272_ = 0;
v_env_273_ = l_Lean_Environment_setRecordingDeps(v_env_271_, v___x_272_);
v___x_274_ = lean_st_ref_get(v___y_266_);
v_toCold_275_ = lean_ctor_get(v___y_267_, 0);
v_mctx_276_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_mctx_276_);
lean_dec(v___x_274_);
v_lctx_277_ = lean_ctor_get(v___y_265_, 2);
v_options_278_ = lean_ctor_get(v_toCold_275_, 2);
lean_inc_ref(v_options_278_);
lean_inc_ref(v_lctx_277_);
v___x_279_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_279_, 0, v_env_273_);
lean_ctor_set(v___x_279_, 1, v_mctx_276_);
lean_ctor_set(v___x_279_, 2, v_lctx_277_);
lean_ctor_set(v___x_279_, 3, v_options_278_);
v___x_280_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_msgData_264_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msgData_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_289_; double v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_float_of_nat(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* v_cls_294_, lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_ref_301_; lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_348_; 
v_ref_301_ = lean_ctor_get(v___y_298_, 2);
v___x_302_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_348_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_348_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_348_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v_traceState_308_; lean_object* v_env_309_; lean_object* v_nextMacroScope_310_; lean_object* v_ngen_311_; lean_object* v_auxDeclNGen_312_; lean_object* v_cache_313_; lean_object* v_recordedDeps_314_; lean_object* v_messages_315_; lean_object* v_infoState_316_; lean_object* v_snapshotTasks_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_347_; 
v___x_307_ = lean_st_ref_take(v___y_299_);
v_traceState_308_ = lean_ctor_get(v___x_307_, 4);
v_env_309_ = lean_ctor_get(v___x_307_, 0);
v_nextMacroScope_310_ = lean_ctor_get(v___x_307_, 1);
v_ngen_311_ = lean_ctor_get(v___x_307_, 2);
v_auxDeclNGen_312_ = lean_ctor_get(v___x_307_, 3);
v_cache_313_ = lean_ctor_get(v___x_307_, 5);
v_recordedDeps_314_ = lean_ctor_get(v___x_307_, 6);
v_messages_315_ = lean_ctor_get(v___x_307_, 7);
v_infoState_316_ = lean_ctor_get(v___x_307_, 8);
v_snapshotTasks_317_ = lean_ctor_get(v___x_307_, 9);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_347_ == 0)
{
v___x_319_ = v___x_307_;
v_isShared_320_ = v_isSharedCheck_347_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snapshotTasks_317_);
lean_inc(v_infoState_316_);
lean_inc(v_messages_315_);
lean_inc(v_recordedDeps_314_);
lean_inc(v_cache_313_);
lean_inc(v_traceState_308_);
lean_inc(v_auxDeclNGen_312_);
lean_inc(v_ngen_311_);
lean_inc(v_nextMacroScope_310_);
lean_inc(v_env_309_);
lean_dec(v___x_307_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_347_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint64_t v_tid_321_; lean_object* v_traces_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_346_; 
v_tid_321_ = lean_ctor_get_uint64(v_traceState_308_, sizeof(void*)*1);
v_traces_322_ = lean_ctor_get(v_traceState_308_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_traceState_308_);
if (v_isSharedCheck_346_ == 0)
{
v___x_324_ = v_traceState_308_;
v_isShared_325_ = v_isSharedCheck_346_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_traces_322_);
lean_dec(v_traceState_308_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_346_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; double v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_326_ = lean_box(0);
v___x_327_ = lean_box(0);
v___x_328_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
v___x_329_ = 0;
v___x_330_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1));
v___x_331_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_331_, 0, v_cls_294_);
lean_ctor_set(v___x_331_, 1, v___x_327_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
lean_ctor_set_float(v___x_331_, sizeof(void*)*3, v___x_328_);
lean_ctor_set_float(v___x_331_, sizeof(void*)*3 + 8, v___x_328_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*3 + 16, v___x_329_);
v___x_332_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2));
v___x_333_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v_a_303_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
lean_inc(v_ref_301_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_ref_301_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_PersistentArray_push___redArg(v_traces_322_, v___x_334_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_335_);
v___x_337_ = v___x_324_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_335_);
lean_ctor_set_uint64(v_reuseFailAlloc_345_, sizeof(void*)*1, v_tid_321_);
v___x_337_ = v_reuseFailAlloc_345_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 4, v___x_337_);
v___x_339_ = v___x_319_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_env_309_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_nextMacroScope_310_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_ngen_311_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_auxDeclNGen_312_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v_cache_313_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_recordedDeps_314_);
lean_ctor_set(v_reuseFailAlloc_344_, 7, v_messages_315_);
lean_ctor_set(v_reuseFailAlloc_344_, 8, v_infoState_316_);
lean_ctor_set(v_reuseFailAlloc_344_, 9, v_snapshotTasks_317_);
v___x_339_ = v_reuseFailAlloc_344_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_st_ref_put(v___y_299_, v___x_339_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_326_);
v___x_342_ = v___x_305_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_326_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* v_cls_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_349_, v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_box(0);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__1));
v___x_364_ = l_Lean_mkConst(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7(void){
_start:
{
lean_object* v_cls_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_cls_372_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_373_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_374_ = l_Lean_Name_append(v___x_373_, v_cls_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__8));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__10));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__12));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
if (lean_obj_tag(v_e_384_) == 7)
{
lean_object* v_binderName_396_; lean_object* v_binderType_397_; lean_object* v_body_398_; uint8_t v_binderInfo_399_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; uint8_t v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v_toCold_425_; lean_object* v_inheritedTraceOptions_426_; lean_object* v_cls_427_; uint8_t v___y_429_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___x_534_; lean_object* v_a_535_; uint8_t v___x_536_; 
v_binderName_396_ = lean_ctor_get(v_e_384_, 0);
v_binderType_397_ = lean_ctor_get(v_e_384_, 1);
v_body_398_ = lean_ctor_get(v_e_384_, 2);
v_binderInfo_399_ = lean_ctor_get_uint8(v_e_384_, sizeof(void*)*3 + 8);
v_toCold_425_ = lean_ctor_get(v_a_393_, 0);
v_inheritedTraceOptions_426_ = lean_ctor_get(v_toCold_425_, 11);
v_cls_427_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___closed__6));
v___x_534_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_427_, v_inheritedTraceOptions_426_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref(v___x_534_);
v___x_536_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
if (v___x_536_ == 0)
{
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
v___y_499_ = v_a_392_;
v___y_500_ = v_a_393_;
v___y_501_ = v_a_394_;
goto v___jp_491_;
}
else
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Grind_updateLastTag(v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_537_, 1);
lean_inc_ref(v_e_384_);
v___x_538_ = l_Lean_MessageData_ofExpr(v_e_384_);
v___x_539_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_427_, v___x_538_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_dec_ref_known(v___x_539_, 1);
v___y_492_ = v_a_385_;
v___y_493_ = v_a_386_;
v___y_494_ = v_a_387_;
v___y_495_ = v_a_388_;
v___y_496_ = v_a_389_;
v___y_497_ = v_a_390_;
v___y_498_ = v_a_391_;
v___y_499_ = v_a_392_;
v___y_500_ = v_a_393_;
v___y_501_ = v_a_394_;
goto v___jp_491_;
}
else
{
lean_dec_ref_known(v_e_384_, 3);
return v___x_539_;
}
}
else
{
lean_dec_ref_known(v_e_384_, 3);
return v___x_537_;
}
}
v___jp_400_:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Simp_Result_getProof(v___y_404_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v___x_414_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__2, &l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
lean_inc_ref(v___y_402_);
lean_inc_ref(v_binderType_397_);
v___x_415_ = l_Lean_mkApp5(v___x_414_, v_binderType_397_, v___y_403_, v___y_402_, v___y_401_, v_a_413_);
v___x_416_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_384_, v___y_402_, v___x_415_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v___x_416_;
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec_ref_known(v_e_384_, 3);
v_a_417_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_412_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
v___jp_428_:
{
lean_object* v___x_440_; 
lean_inc_ref(v_binderType_397_);
v___x_440_ = l_Lean_Meta_Grind_mkEqTrueProof(v_binderType_397_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc_n(v_a_441_, 2);
lean_dec_ref_known(v___x_440_, 1);
lean_inc_ref(v_binderType_397_);
v___x_442_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_397_, v_a_441_);
v___x_443_ = lean_expr_instantiate1(v_body_398_, v___x_442_);
lean_dec_ref(v___x_442_);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc(v___y_430_);
v___x_444_ = lean_grind_preprocess(v___x_443_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_expr_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v_expr_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc_ref(v_expr_446_);
lean_inc_ref(v_body_398_);
lean_inc_ref(v_binderType_397_);
lean_inc(v_binderName_396_);
v___x_447_ = l_Lean_mkLambda(v_binderName_396_, v_binderInfo_399_, v_binderType_397_, v_body_398_);
v___x_448_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_384_, v___y_430_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = lean_box(0);
lean_inc(v___y_439_);
lean_inc_ref(v___y_438_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc(v___y_435_);
lean_inc_ref(v___y_434_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_expr_446_);
v___x_451_ = lean_grind_internalize(v_expr_446_, v_a_449_, v___x_450_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_toCold_452_; lean_object* v_options_453_; uint8_t v_hasTrace_454_; 
lean_dec_ref_known(v___x_451_, 1);
v_toCold_452_ = lean_ctor_get(v___y_438_, 0);
v_options_453_ = lean_ctor_get(v_toCold_452_, 2);
v_hasTrace_454_ = lean_ctor_get_uint8(v_options_453_, sizeof(void*)*1);
if (v_hasTrace_454_ == 0)
{
v___y_401_ = v_a_441_;
v___y_402_ = v_expr_446_;
v___y_403_ = v___x_447_;
v___y_404_ = v_a_445_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_430_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
v___y_410_ = v___y_438_;
v___y_411_ = v___y_439_;
goto v___jp_400_;
}
else
{
lean_object* v_inheritedTraceOptions_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_inheritedTraceOptions_455_ = lean_ctor_get(v_toCold_452_, 11);
v___x_456_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__7, &l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
v___x_457_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_455_, v_options_453_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_401_ = v_a_441_;
v___y_402_ = v_expr_446_;
v___y_403_ = v___x_447_;
v___y_404_ = v_a_445_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_430_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
v___y_410_ = v___y_438_;
v___y_411_ = v___y_439_;
goto v___jp_400_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Grind_updateLastTag(v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref_known(v___x_458_, 1);
v___x_459_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__9, &l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
lean_inc_ref(v_expr_446_);
v___x_460_ = l_Lean_MessageData_ofExpr(v_expr_446_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__11, &l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
lean_inc_ref(v_e_384_);
v___x_464_ = l_Lean_indentExpr(v_e_384_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_427_, v___x_465_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_dec_ref_known(v___x_466_, 1);
v___y_401_ = v_a_441_;
v___y_402_ = v_expr_446_;
v___y_403_ = v___x_447_;
v___y_404_ = v_a_445_;
v___y_405_ = v___y_429_;
v___y_406_ = v___y_430_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_436_;
v___y_409_ = v___y_437_;
v___y_410_ = v___y_438_;
v___y_411_ = v___y_439_;
goto v___jp_400_;
}
else
{
lean_dec_ref(v___x_447_);
lean_dec_ref(v_expr_446_);
lean_dec(v_a_445_);
lean_dec(v_a_441_);
lean_dec_ref_known(v_e_384_, 3);
return v___x_466_;
}
}
else
{
lean_dec_ref(v___x_447_);
lean_dec_ref(v_expr_446_);
lean_dec(v_a_445_);
lean_dec(v_a_441_);
lean_dec_ref_known(v_e_384_, 3);
return v___x_458_;
}
}
}
}
else
{
lean_dec_ref(v___x_447_);
lean_dec_ref(v_expr_446_);
lean_dec(v_a_445_);
lean_dec(v_a_441_);
lean_dec_ref_known(v_e_384_, 3);
return v___x_451_;
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v___x_447_);
lean_dec_ref(v_expr_446_);
lean_dec(v_a_445_);
lean_dec(v_a_441_);
lean_dec_ref_known(v_e_384_, 3);
v_a_467_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_448_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_448_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_a_441_);
lean_dec_ref_known(v_e_384_, 3);
v_a_475_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_444_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_444_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref_known(v_e_384_, 3);
v_a_483_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_440_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_440_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
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
v___jp_491_:
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_Expr_hasLooseBVars(v_body_398_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_inc_ref(v_body_398_);
lean_inc_ref(v_binderType_397_);
v___x_503_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_384_, v_binderType_397_, v_body_398_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
else
{
uint8_t v___x_504_; lean_object* v___x_505_; 
v___x_504_ = 0;
lean_inc_ref(v_binderType_397_);
v___x_505_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_binderType_397_, v___y_492_, v___y_496_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_525_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_525_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint8_t v___x_510_; 
v___x_510_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec_ref_known(v_e_384_, 3);
v___x_511_ = lean_box(0);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
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
lean_object* v_toCold_515_; lean_object* v_inheritedTraceOptions_516_; lean_object* v___x_517_; lean_object* v_a_518_; uint8_t v___x_519_; 
lean_del_object(v___x_508_);
v_toCold_515_ = lean_ctor_get(v___y_500_, 0);
v_inheritedTraceOptions_516_ = lean_ctor_get(v_toCold_515_, 11);
v___x_517_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(v_cls_427_, v_inheritedTraceOptions_516_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
v___y_429_ = v___x_504_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
v___y_437_ = v___y_499_;
v___y_438_ = v___y_500_;
v___y_439_ = v___y_501_;
goto v___jp_428_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_Grind_updateLastTag(v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v___x_520_, 1);
v___x_521_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropUp___closed__13, &l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once, _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
lean_inc_ref(v_e_384_);
v___x_522_ = l_Lean_MessageData_ofExpr(v_e_384_);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_427_, v___x_523_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_dec_ref_known(v___x_524_, 1);
v___y_429_ = v___x_504_;
v___y_430_ = v___y_492_;
v___y_431_ = v___y_493_;
v___y_432_ = v___y_494_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_496_;
v___y_435_ = v___y_497_;
v___y_436_ = v___y_498_;
v___y_437_ = v___y_499_;
v___y_438_ = v___y_500_;
v___y_439_ = v___y_501_;
goto v___jp_428_;
}
else
{
lean_dec_ref_known(v_e_384_, 3);
return v___x_524_;
}
}
else
{
lean_dec_ref_known(v_e_384_, 3);
return v___x_520_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref_known(v_e_384_, 3);
v_a_526_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_505_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_505_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec_ref(v_e_384_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_Grind_propagateForallPropUp(v_e_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec(v_a_543_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* v_cls_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_555_, v_msg_556_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* v_cls_569_, lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(v_cls_569_, v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec(v___y_571_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* v_origin_585_, lean_object* v_proof_586_, lean_object* v_kind_587_, lean_object* v_prios_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; 
v___x_594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0));
v___x_595_ = 0;
v___x_596_ = 1;
v___x_597_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v_origin_585_, v___x_594_, v_proof_586_, v_kind_587_, v_prios_588_, v___x_595_, v___x_595_, v___x_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_597_) == 0)
{
return v___x_597_;
}
else
{
lean_object* v_a_598_; uint8_t v___y_600_; uint8_t v___x_610_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v___x_610_ = l_Lean_Exception_isInterrupt(v_a_598_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; 
lean_inc(v_a_598_);
v___x_611_ = l_Lean_Exception_isRuntime(v_a_598_);
v___y_600_ = v___x_611_;
goto v___jp_599_;
}
else
{
v___y_600_ = v___x_610_;
goto v___jp_599_;
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_597_, 0);
lean_dec(v_unused_609_);
v___x_602_ = v___x_597_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_dec(v___x_597_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 0);
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* v_origin_612_, lean_object* v_proof_613_, lean_object* v_kind_614_, lean_object* v_prios_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_612_, v_proof_613_, v_kind_614_, v_prios_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
if (lean_obj_tag(v_x_623_) == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 1;
return v___x_624_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
else
{
if (lean_obj_tag(v_x_623_) == 0)
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v_head_629_; lean_object* v_tail_630_; uint8_t v___x_631_; 
v_head_627_ = lean_ctor_get(v_x_622_, 0);
v_tail_628_ = lean_ctor_get(v_x_622_, 1);
v_head_629_ = lean_ctor_get(v_x_623_, 0);
v_tail_630_ = lean_ctor_get(v_x_623_, 1);
v___x_631_ = lean_expr_eqv(v_head_627_, v_head_629_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
v_x_622_ = v_tail_628_;
v_x_623_ = v_tail_630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec(v_x_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* v_thm_x27_637_, lean_object* v_as_638_, size_t v_i_639_, size_t v_stop_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_eq(v_i_639_, v_stop_640_);
if (v___x_641_ == 0)
{
lean_object* v_patterns_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_patterns_642_ = lean_ctor_get(v_thm_x27_637_, 3);
v___x_643_ = lean_array_uget_borrowed(v_as_638_, v_i_639_);
v___x_644_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_642_, v___x_643_);
if (v___x_644_ == 0)
{
size_t v___x_645_; size_t v___x_646_; 
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_639_, v___x_645_);
v_i_639_ = v___x_646_;
goto _start;
}
else
{
return v___x_644_;
}
}
else
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* v_thm_x27_649_, lean_object* v_as_650_, lean_object* v_i_651_, lean_object* v_stop_652_){
_start:
{
size_t v_i_boxed_653_; size_t v_stop_boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v_i_boxed_653_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_stop_boxed_654_ = lean_unbox_usize(v_stop_652_);
lean_dec(v_stop_652_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_649_, v_as_650_, v_i_boxed_653_, v_stop_boxed_654_);
lean_dec_ref(v_as_650_);
lean_dec_ref(v_thm_x27_649_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* v_patternsFoundSoFar_657_, lean_object* v_thm_x27_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_array_get_size(v_patternsFoundSoFar_657_);
v___x_661_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 1;
return v___x_662_;
}
else
{
if (v___x_661_ == 0)
{
return v___x_661_;
}
else
{
size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_660_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_658_, v_patternsFoundSoFar_657_, v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
return v___x_661_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* v_patternsFoundSoFar_667_, lean_object* v_thm_x27_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_667_, v_thm_x27_668_);
lean_dec_ref(v_thm_x27_668_);
lean_dec_ref(v_patternsFoundSoFar_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(lean_object* v_proof_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___y_687_; lean_object* v___x_754_; 
lean_inc_ref(v_proof_682_);
v___x_754_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_682_, v_a_684_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = l_Lean_Expr_cleanupAnnotations(v_a_755_);
v___x_757_ = l_Lean_Expr_isApp(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec_ref(v___x_756_);
v___y_687_ = v_a_683_;
goto v___jp_686_;
}
else
{
lean_object* v_arg_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_arg_758_ = lean_ctor_get(v___x_756_, 1);
lean_inc_ref(v_arg_758_);
v___x_759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_756_);
v___x_760_ = l_Lean_Expr_isApp(v___x_759_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_759_);
lean_dec_ref(v_arg_758_);
v___y_687_ = v_a_683_;
goto v___jp_686_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_759_);
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3));
v___x_763_ = l_Lean_Expr_isConstOf(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
uint8_t v___x_764_; 
v___x_764_ = l_Lean_Expr_isApp(v___x_761_);
if (v___x_764_ == 0)
{
lean_dec_ref(v___x_761_);
lean_dec_ref(v_arg_758_);
v___y_687_ = v_a_683_;
goto v___jp_686_;
}
else
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_761_);
v___x_766_ = l_Lean_Expr_isApp(v___x_765_);
if (v___x_766_ == 0)
{
lean_dec_ref(v___x_765_);
lean_dec_ref(v_arg_758_);
v___y_687_ = v_a_683_;
goto v___jp_686_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_765_);
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6));
v___x_769_ = l_Lean_Expr_isConstOf(v___x_767_, v___x_768_);
lean_dec_ref(v___x_767_);
if (v___x_769_ == 0)
{
lean_dec_ref(v_arg_758_);
v___y_687_ = v_a_683_;
goto v___jp_686_;
}
else
{
lean_dec_ref(v_proof_682_);
v_proof_682_ = v_arg_758_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v___x_761_);
lean_dec_ref(v_proof_682_);
v_proof_682_ = v_arg_758_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_proof_682_);
v_a_772_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_754_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_754_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
v___jp_686_:
{
if (lean_obj_tag(v_proof_682_) == 1)
{
lean_object* v_fvarId_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_fvarId_688_ = lean_ctor_get(v_proof_682_, 0);
lean_inc(v_fvarId_688_);
lean_dec_ref_known(v_proof_682_, 1);
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_fvarId_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v_toGoalState_692_; lean_object* v_ematch_693_; lean_object* v_mvarId_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_proof_682_);
v___x_691_ = lean_st_ref_take(v___y_687_);
v_toGoalState_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_toGoalState_692_);
v_ematch_693_ = lean_ctor_get(v_toGoalState_692_, 13);
lean_inc_ref(v_ematch_693_);
v_mvarId_694_ = lean_ctor_get(v___x_691_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_691_, 0);
lean_dec(v_unused_753_);
v___x_696_ = v___x_691_;
v_isShared_697_ = v_isSharedCheck_752_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_mvarId_694_);
lean_dec(v___x_691_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_752_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_nextDeclIdx_698_; lean_object* v_enodeMap_699_; lean_object* v_exprs_700_; lean_object* v_parents_701_; lean_object* v_congrTable_702_; lean_object* v_appMap_703_; lean_object* v_indicesFound_704_; lean_object* v_toProcess_705_; lean_object* v_internalizing_706_; uint8_t v_inconsistent_707_; lean_object* v_nextIdx_708_; lean_object* v_newRawFacts_709_; lean_object* v_facts_710_; lean_object* v_extThms_711_; lean_object* v_inj_712_; lean_object* v_split_713_; lean_object* v_clean_714_; lean_object* v_sstates_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_750_; 
v_nextDeclIdx_698_ = lean_ctor_get(v_toGoalState_692_, 0);
v_enodeMap_699_ = lean_ctor_get(v_toGoalState_692_, 1);
v_exprs_700_ = lean_ctor_get(v_toGoalState_692_, 2);
v_parents_701_ = lean_ctor_get(v_toGoalState_692_, 3);
v_congrTable_702_ = lean_ctor_get(v_toGoalState_692_, 4);
v_appMap_703_ = lean_ctor_get(v_toGoalState_692_, 5);
v_indicesFound_704_ = lean_ctor_get(v_toGoalState_692_, 6);
v_toProcess_705_ = lean_ctor_get(v_toGoalState_692_, 7);
v_internalizing_706_ = lean_ctor_get(v_toGoalState_692_, 8);
v_inconsistent_707_ = lean_ctor_get_uint8(v_toGoalState_692_, sizeof(void*)*18);
v_nextIdx_708_ = lean_ctor_get(v_toGoalState_692_, 9);
v_newRawFacts_709_ = lean_ctor_get(v_toGoalState_692_, 10);
v_facts_710_ = lean_ctor_get(v_toGoalState_692_, 11);
v_extThms_711_ = lean_ctor_get(v_toGoalState_692_, 12);
v_inj_712_ = lean_ctor_get(v_toGoalState_692_, 14);
v_split_713_ = lean_ctor_get(v_toGoalState_692_, 15);
v_clean_714_ = lean_ctor_get(v_toGoalState_692_, 16);
v_sstates_715_ = lean_ctor_get(v_toGoalState_692_, 17);
v_isSharedCheck_750_ = !lean_is_exclusive(v_toGoalState_692_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_toGoalState_692_, 13);
lean_dec(v_unused_751_);
v___x_717_ = v_toGoalState_692_;
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_sstates_715_);
lean_inc(v_clean_714_);
lean_inc(v_split_713_);
lean_inc(v_inj_712_);
lean_inc(v_extThms_711_);
lean_inc(v_facts_710_);
lean_inc(v_newRawFacts_709_);
lean_inc(v_nextIdx_708_);
lean_inc(v_internalizing_706_);
lean_inc(v_toProcess_705_);
lean_inc(v_indicesFound_704_);
lean_inc(v_appMap_703_);
lean_inc(v_congrTable_702_);
lean_inc(v_parents_701_);
lean_inc(v_exprs_700_);
lean_inc(v_enodeMap_699_);
lean_inc(v_nextDeclIdx_698_);
lean_dec(v_toGoalState_692_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_thmMap_719_; lean_object* v_gmt_720_; lean_object* v_thms_721_; lean_object* v_newThms_722_; lean_object* v_numInstances_723_; lean_object* v_numDelayedInstances_724_; lean_object* v_num_725_; lean_object* v_preInstances_726_; lean_object* v_nextThmIdx_727_; lean_object* v_matchEqNames_728_; lean_object* v_delayedThmInsts_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_749_; 
v_thmMap_719_ = lean_ctor_get(v_ematch_693_, 0);
v_gmt_720_ = lean_ctor_get(v_ematch_693_, 1);
v_thms_721_ = lean_ctor_get(v_ematch_693_, 2);
v_newThms_722_ = lean_ctor_get(v_ematch_693_, 3);
v_numInstances_723_ = lean_ctor_get(v_ematch_693_, 4);
v_numDelayedInstances_724_ = lean_ctor_get(v_ematch_693_, 5);
v_num_725_ = lean_ctor_get(v_ematch_693_, 6);
v_preInstances_726_ = lean_ctor_get(v_ematch_693_, 7);
v_nextThmIdx_727_ = lean_ctor_get(v_ematch_693_, 8);
v_matchEqNames_728_ = lean_ctor_get(v_ematch_693_, 9);
v_delayedThmInsts_729_ = lean_ctor_get(v_ematch_693_, 10);
v_isSharedCheck_749_ = !lean_is_exclusive(v_ematch_693_);
if (v_isSharedCheck_749_ == 0)
{
v___x_731_ = v_ematch_693_;
v_isShared_732_ = v_isSharedCheck_749_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_delayedThmInsts_729_);
lean_inc(v_matchEqNames_728_);
lean_inc(v_nextThmIdx_727_);
lean_inc(v_preInstances_726_);
lean_inc(v_num_725_);
lean_inc(v_numDelayedInstances_724_);
lean_inc(v_numInstances_723_);
lean_inc(v_newThms_722_);
lean_inc(v_thms_721_);
lean_inc(v_gmt_720_);
lean_inc(v_thmMap_719_);
lean_dec(v_ematch_693_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_749_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_add(v_nextThmIdx_727_, v___x_733_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 8, v___x_734_);
v___x_736_ = v___x_731_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_thmMap_719_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_gmt_720_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_thms_721_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_newThms_722_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_numInstances_723_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v_numDelayedInstances_724_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_num_725_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v_preInstances_726_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 9, v_matchEqNames_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 10, v_delayedThmInsts_729_);
v___x_736_ = v_reuseFailAlloc_748_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 13, v___x_736_);
v___x_738_ = v___x_717_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_nextDeclIdx_698_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_enodeMap_699_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_exprs_700_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_parents_701_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_congrTable_702_);
lean_ctor_set(v_reuseFailAlloc_747_, 5, v_appMap_703_);
lean_ctor_set(v_reuseFailAlloc_747_, 6, v_indicesFound_704_);
lean_ctor_set(v_reuseFailAlloc_747_, 7, v_toProcess_705_);
lean_ctor_set(v_reuseFailAlloc_747_, 8, v_internalizing_706_);
lean_ctor_set(v_reuseFailAlloc_747_, 9, v_nextIdx_708_);
lean_ctor_set(v_reuseFailAlloc_747_, 10, v_newRawFacts_709_);
lean_ctor_set(v_reuseFailAlloc_747_, 11, v_facts_710_);
lean_ctor_set(v_reuseFailAlloc_747_, 12, v_extThms_711_);
lean_ctor_set(v_reuseFailAlloc_747_, 13, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 14, v_inj_712_);
lean_ctor_set(v_reuseFailAlloc_747_, 15, v_split_713_);
lean_ctor_set(v_reuseFailAlloc_747_, 16, v_clean_714_);
lean_ctor_set(v_reuseFailAlloc_747_, 17, v_sstates_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_747_, sizeof(void*)*18, v_inconsistent_707_);
v___x_738_ = v_reuseFailAlloc_747_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_738_);
v___x_740_ = v___x_696_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_mvarId_694_);
v___x_740_ = v_reuseFailAlloc_746_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_741_ = lean_st_ref_put(v___y_687_, v___x_740_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1));
v___x_743_ = lean_name_append_index_after(v___x_742_, v_nextThmIdx_727_);
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(lean_object* v_proof_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec(v_a_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(lean_object* v_proof_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_proof_785_, v_a_786_, v_a_793_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(lean_object* v_proof_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(v_proof_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t v_a_811_, lean_object* v_as_812_, size_t v_i_813_, size_t v_stop_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_eq(v_i_813_, v_stop_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_array_uget_borrowed(v_as_812_, v_i_813_);
v___x_817_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_816_, v_a_811_);
if (v___x_817_ == 0)
{
size_t v___x_818_; size_t v___x_819_; 
v___x_818_ = ((size_t)1ULL);
v___x_819_ = lean_usize_add(v_i_813_, v___x_818_);
v_i_813_ = v___x_819_;
goto _start;
}
else
{
return v___x_817_;
}
}
else
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* v_a_822_, lean_object* v_as_823_, lean_object* v_i_824_, lean_object* v_stop_825_){
_start:
{
uint64_t v_a_3837__boxed_826_; size_t v_i_boxed_827_; size_t v_stop_boxed_828_; uint8_t v_res_829_; lean_object* v_r_830_; 
v_a_3837__boxed_826_ = lean_unbox_uint64(v_a_822_);
lean_dec_ref(v_a_822_);
v_i_boxed_827_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_stop_boxed_828_ = lean_unbox_usize(v_stop_825_);
lean_dec(v_stop_825_);
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_3837__boxed_826_, v_as_823_, v_i_boxed_827_, v_stop_boxed_828_);
lean_dec_ref(v_as_823_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* v_proof_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_833_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_896_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_896_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_896_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_896_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
if (lean_obj_tag(v_a_843_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; 
lean_del_object(v___x_845_);
v_val_847_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_a_843_, 1);
lean_inc(v_a_840_);
lean_inc_ref(v_a_839_);
lean_inc(v_a_838_);
lean_inc_ref(v_a_837_);
v___x_848_ = lean_infer_type(v_proof_831_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = l_Lean_Meta_Grind_getAnchor(v_a_849_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_874_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_874_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_874_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_874_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_array_get_size(v_val_847_);
v___x_857_ = lean_nat_dec_lt(v___x_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_a_851_);
lean_dec(v_val_847_);
v___x_858_ = lean_box(v___x_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_858_);
v___x_860_ = v___x_853_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
if (v___x_857_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v_a_851_);
lean_dec(v_val_847_);
v___x_862_ = lean_box(v___x_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_862_);
v___x_864_ = v___x_853_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
size_t v___x_866_; size_t v___x_867_; uint64_t v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_866_ = ((size_t)0ULL);
v___x_867_ = lean_usize_of_nat(v___x_856_);
v___x_868_ = lean_unbox_uint64(v_a_851_);
lean_dec(v_a_851_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_868_, v_val_847_, v___x_866_, v___x_867_);
lean_dec(v_val_847_);
v___x_870_ = lean_box(v___x_869_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_870_);
v___x_872_ = v___x_853_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_val_847_);
v_a_875_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_850_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_850_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_val_847_);
v_a_883_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_848_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_848_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v_a_843_);
lean_dec_ref(v_proof_831_);
v___x_891_ = 1;
v___x_892_ = lean_box(v___x_891_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_892_);
v___x_894_ = v___x_845_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_proof_831_);
v_a_897_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_842_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_842_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* v_proof_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* v_a_917_, lean_object* v_as_918_, size_t v_sz_919_, size_t v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_a_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec(v_a_917_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_921_);
return v___x_939_;
}
else
{
lean_object* v_a_940_; uint8_t v___x_941_; 
v_a_940_ = lean_array_uget_borrowed(v_as_918_, v_i_920_);
v___x_941_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_b_921_, v_a_940_);
if (v___x_941_ == 0)
{
v_a_934_ = v_b_921_;
goto v___jp_933_;
}
else
{
lean_object* v___x_942_; 
lean_inc(v_a_917_);
lean_inc(v_a_940_);
v___x_942_ = l_Lean_Meta_Grind_activateTheorem(v_a_940_, v_a_917_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_patterns_943_; lean_object* v___x_944_; 
lean_dec_ref_known(v___x_942_, 1);
v_patterns_943_ = lean_ctor_get(v_a_940_, 3);
lean_inc(v_patterns_943_);
v___x_944_ = lean_array_push(v_b_921_, v_patterns_943_);
v_a_934_ = v___x_944_;
goto v___jp_933_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v_b_921_);
lean_dec(v_a_917_);
v_a_945_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_942_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_942_);
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
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_920_, v___x_935_);
v_i_920_ = v___x_936_;
v_b_921_ = v_a_934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* v_a_953_, lean_object* v_as_954_, lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_970_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_953_, v_as_954_, v_sz_boxed_969_, v_i_boxed_970_, v_b_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v_as_954_);
return v_res_971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* v_e_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
lean_inc_ref(v_e_979_);
v___x_991_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc_n(v_a_992_, 2);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_a_992_, v_a_980_, v_a_987_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
lean_inc_ref(v_e_979_);
v___x_995_ = l_Lean_Meta_mkOfEqTrueCore(v_e_979_, v_a_992_);
lean_inc_ref(v___x_995_);
v___x_996_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v___x_995_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1176_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1176_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1176_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_unbox(v_a_997_);
lean_dec(v_a_997_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v___x_1002_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v_toGoalState_1007_; lean_object* v_ematch_1008_; lean_object* v_newThms_1009_; lean_object* v_size_1010_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___x_1059_; 
v___x_1006_ = lean_st_ref_get(v_a_980_);
v_toGoalState_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_ref(v_toGoalState_1007_);
lean_dec(v___x_1006_);
v_ematch_1008_ = lean_ctor_get(v_toGoalState_1007_, 13);
lean_inc_ref(v_ematch_1008_);
lean_dec_ref(v_toGoalState_1007_);
v_newThms_1009_ = lean_ctor_get(v_ematch_1008_, 3);
lean_inc_ref(v_newThms_1009_);
lean_dec_ref(v_ematch_1008_);
v_size_1010_ = lean_ctor_get(v_newThms_1009_, 2);
lean_inc(v_size_1010_);
lean_dec_ref(v_newThms_1009_);
v___x_1059_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_979_, v_a_980_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2));
v___x_1062_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v_a_982_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v_patternsFoundSoFar_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___x_1122_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_n(v_a_1063_, 2);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_unsigned_to_nat(1000u);
v___x_1065_ = 0;
lean_inc_ref(v___x_995_);
lean_inc(v_a_994_);
v___x_1122_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(v_a_994_, v___x_1061_, v___x_995_, v___x_1064_, v_a_1063_, v___x_1065_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v_sz_1124_ = lean_array_size(v_a_1123_);
v___x_1125_ = ((size_t)0ULL);
lean_inc(v_a_1060_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_1060_, v_a_1123_, v_sz_1124_, v___x_1125_, v___x_1061_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = lean_box(6);
lean_inc(v_a_1063_);
lean_inc_ref(v___x_995_);
lean_inc(v_a_994_);
v___x_1129_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_994_, v___x_995_, v___x_1128_, v_a_1063_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
if (lean_obj_tag(v_a_1130_) == 1)
{
lean_object* v_val_1131_; uint8_t v___x_1132_; 
v_val_1131_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v_a_1130_, 1);
v___x_1132_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_a_1127_, v_val_1131_);
if (v___x_1132_ == 0)
{
lean_dec(v_val_1131_);
v_patternsFoundSoFar_1097_ = v_a_1127_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
v___y_1105_ = v_a_987_;
v___y_1106_ = v_a_988_;
v___y_1107_ = v_a_989_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1133_; 
lean_inc(v_a_1060_);
lean_inc(v_val_1131_);
v___x_1133_ = l_Lean_Meta_Grind_activateTheorem(v_val_1131_, v_a_1060_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_patterns_1134_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1133_, 1);
v_patterns_1134_ = lean_ctor_get(v_val_1131_, 3);
lean_inc(v_patterns_1134_);
lean_dec(v_val_1131_);
v___x_1135_ = lean_array_push(v_a_1127_, v_patterns_1134_);
v_patternsFoundSoFar_1097_ = v___x_1135_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
v___y_1105_ = v_a_987_;
v___y_1106_ = v_a_988_;
v___y_1107_ = v_a_989_;
goto v___jp_1096_;
}
else
{
lean_dec(v_val_1131_);
lean_dec(v_a_1127_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
return v___x_1133_;
}
}
}
else
{
lean_dec(v_a_1130_);
v_patternsFoundSoFar_1097_ = v_a_1127_;
v___y_1098_ = v_a_980_;
v___y_1099_ = v_a_981_;
v___y_1100_ = v_a_982_;
v___y_1101_ = v_a_983_;
v___y_1102_ = v_a_984_;
v___y_1103_ = v_a_985_;
v___y_1104_ = v_a_986_;
v___y_1105_ = v_a_987_;
v___y_1106_ = v_a_988_;
v___y_1107_ = v_a_989_;
goto v___jp_1096_;
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1127_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1136_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1129_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1129_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1144_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1126_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1126_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1152_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1122_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1122_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1077_; lean_object* v_toGoalState_1078_; lean_object* v_ematch_1079_; lean_object* v_newThms_1080_; lean_object* v_size_1081_; uint8_t v___x_1082_; 
v___x_1077_ = lean_st_ref_get(v___y_1067_);
v_toGoalState_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_toGoalState_1078_);
lean_dec(v___x_1077_);
v_ematch_1079_ = lean_ctor_get(v_toGoalState_1078_, 13);
lean_inc_ref(v_ematch_1079_);
lean_dec_ref(v_toGoalState_1078_);
v_newThms_1080_ = lean_ctor_get(v_ematch_1079_, 3);
lean_inc_ref(v_newThms_1080_);
lean_dec_ref(v_ematch_1079_);
v_size_1081_ = lean_ctor_get(v_newThms_1080_, 2);
lean_inc(v_size_1081_);
lean_dec_ref(v_newThms_1080_);
v___x_1082_ = lean_nat_dec_eq(v_size_1081_, v_size_1010_);
lean_dec(v_size_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
v___y_1012_ = v___y_1067_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
v___y_1016_ = v___y_1074_;
v___y_1017_ = v___y_1075_;
v___y_1018_ = v___y_1076_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3));
v___x_1084_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_994_, v___x_995_, v___x_1083_, v_a_1063_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
v_val_1086_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1085_, 1);
v___x_1087_ = l_Lean_Meta_Grind_activateTheorem(v_val_1086_, v_a_1060_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec_ref_known(v___x_1087_, 1);
v___y_1012_ = v___y_1067_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
v___y_1016_ = v___y_1074_;
v___y_1017_ = v___y_1075_;
v___y_1018_ = v___y_1076_;
goto v___jp_1011_;
}
else
{
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v_e_979_);
return v___x_1087_;
}
}
else
{
lean_dec(v_a_1085_);
lean_dec(v_a_1060_);
v___y_1012_ = v___y_1067_;
v___y_1013_ = v___y_1071_;
v___y_1014_ = v___y_1072_;
v___y_1015_ = v___y_1073_;
v___y_1016_ = v___y_1074_;
v___y_1017_ = v___y_1075_;
v___y_1018_ = v___y_1076_;
goto v___jp_1011_;
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v_e_979_);
v_a_1088_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1084_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1084_);
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
}
v___jp_1096_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(7);
lean_inc(v_a_1063_);
lean_inc_ref(v___x_995_);
lean_inc(v_a_994_);
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_994_, v___x_995_, v___x_1108_, v_a_1063_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
if (lean_obj_tag(v_a_1110_) == 1)
{
lean_object* v_val_1111_; uint8_t v___x_1112_; 
v_val_1111_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v_a_1110_, 1);
v___x_1112_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_1097_, v_val_1111_);
lean_dec_ref(v_patternsFoundSoFar_1097_);
if (v___x_1112_ == 0)
{
lean_dec(v_val_1111_);
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
v___y_1074_ = v___y_1105_;
v___y_1075_ = v___y_1106_;
v___y_1076_ = v___y_1107_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1113_; 
lean_inc(v_a_1060_);
v___x_1113_ = l_Lean_Meta_Grind_activateTheorem(v_val_1111_, v_a_1060_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
v___y_1074_ = v___y_1105_;
v___y_1075_ = v___y_1106_;
v___y_1076_ = v___y_1107_;
goto v___jp_1066_;
}
else
{
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
return v___x_1113_;
}
}
}
else
{
lean_dec(v_a_1110_);
lean_dec_ref(v_patternsFoundSoFar_1097_);
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1099_;
v___y_1069_ = v___y_1100_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1103_;
v___y_1073_ = v___y_1104_;
v___y_1074_ = v___y_1105_;
v___y_1075_ = v___y_1106_;
v___y_1076_ = v___y_1107_;
goto v___jp_1066_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_patternsFoundSoFar_1097_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1114_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1109_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1109_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v_a_1060_);
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1160_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1062_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1062_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_size_1010_);
lean_del_object(v___x_999_);
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1168_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1059_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1059_);
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
v___jp_1011_:
{
lean_object* v___x_1019_; lean_object* v_toGoalState_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1057_; 
v___x_1019_ = lean_st_ref_get(v___y_1012_);
v_toGoalState_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1019_, 1);
lean_dec(v_unused_1058_);
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1057_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_toGoalState_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1057_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_ematch_1024_; lean_object* v_newThms_1025_; lean_object* v_size_1026_; uint8_t v___x_1027_; 
v_ematch_1024_ = lean_ctor_get(v_toGoalState_1020_, 13);
lean_inc_ref(v_ematch_1024_);
lean_dec_ref(v_toGoalState_1020_);
v_newThms_1025_ = lean_ctor_get(v_ematch_1024_, 3);
lean_inc_ref(v_newThms_1025_);
lean_dec_ref(v_ematch_1024_);
v_size_1026_ = lean_ctor_get(v_newThms_1025_, 2);
lean_inc(v_size_1026_);
lean_dec_ref(v_newThms_1025_);
v___x_1027_ = lean_nat_dec_eq(v_size_1026_, v_size_1010_);
lean_dec(v_size_1010_);
lean_dec(v_size_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_del_object(v___x_1022_);
lean_dec_ref(v_e_979_);
v___x_1028_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1028_);
v___x_1030_ = v___x_999_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_del_object(v___x_999_);
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
v___x_1033_ = l_Lean_indentExpr(v_e_979_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 7);
lean_ctor_set(v___x_1022_, 1, v___x_1033_);
lean_ctor_set(v___x_1022_, 0, v___x_1032_);
v___x_1035_ = v___x_1022_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_1013_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1047_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1047_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1047_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint8_t v_verbose_1041_; 
v_verbose_1041_ = lean_ctor_get_uint8(v_a_1037_, 0);
lean_dec(v_a_1037_);
if (v_verbose_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec_ref(v___x_1035_);
v___x_1042_ = lean_box(0);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1042_);
v___x_1044_ = v___x_1039_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v___x_1046_; 
lean_del_object(v___x_1039_);
v___x_1046_ = l_Lean_Meta_Sym_reportIssue(v___x_1035_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1046_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___x_1035_);
v_a_1048_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1036_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1036_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
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
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v___x_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_e_979_);
v_a_1177_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_996_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_996_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_992_);
lean_dec_ref(v_e_979_);
v_a_1185_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_993_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_993_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_e_979_);
v_a_1193_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_991_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_991_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1));
v___x_1220_ = l_Lean_Name_append(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__3));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__10));
v___x_1239_ = l_Lean_mkConst(v___x_1238_, v___x_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__13));
v___x_1247_ = l_Lean_mkConst(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* v_e_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
if (lean_obj_tag(v_e_1248_) == 7)
{
lean_object* v_binderName_1260_; lean_object* v_binderType_1261_; lean_object* v_body_1262_; uint8_t v_binderInfo_1263_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___x_1372_; 
v_binderName_1260_ = lean_ctor_get(v_e_1248_, 0);
v_binderType_1261_ = lean_ctor_get(v_e_1248_, 1);
v_body_1262_ = lean_ctor_get(v_e_1248_, 2);
v_binderInfo_1263_ = lean_ctor_get_uint8(v_e_1248_, sizeof(void*)*3 + 8);
lean_inc_ref(v_e_1248_);
v___x_1372_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1248_, v_a_1249_, v_a_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_inc_ref(v_e_1248_);
v___x_1375_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1248_, v_a_1249_, v_a_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1460_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1460_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1460_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_unbox(v_a_1376_);
lean_dec(v_a_1376_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1381_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1381_);
v___x_1383_ = v___x_1378_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1385_; 
lean_del_object(v___x_1378_);
lean_inc_ref(v_e_1248_);
v___x_1385_ = l_Lean_Meta_Grind_eqResolution(v_e_1248_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
if (lean_obj_tag(v_a_1386_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1451_; 
v_val_1387_ = lean_ctor_get(v_a_1386_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_a_1386_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1389_ = v_a_1386_;
v_isShared_1390_ = v_isSharedCheck_1451_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v_a_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1451_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1450_; 
v_fst_1391_ = lean_ctor_get(v_val_1387_, 0);
v_snd_1392_ = lean_ctor_get(v_val_1387_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_val_1387_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1394_ = v_val_1387_;
v_isShared_1395_ = v_isSharedCheck_1450_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_snd_1392_);
lean_inc(v_fst_1391_);
lean_dec(v_val_1387_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1450_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v_toCold_1434_; lean_object* v_options_1435_; uint8_t v_hasTrace_1436_; 
v_toCold_1434_ = lean_ctor_get(v_a_1257_, 0);
v_options_1435_ = lean_ctor_get(v_toCold_1434_, 2);
v_hasTrace_1436_ = lean_ctor_get_uint8(v_options_1435_, sizeof(void*)*1);
if (v_hasTrace_1436_ == 0)
{
lean_del_object(v___x_1394_);
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
goto v___jp_1396_;
}
else
{
lean_object* v_inheritedTraceOptions_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_inheritedTraceOptions_1437_ = lean_ctor_get(v_toCold_1434_, 11);
v___x_1438_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__1));
v___x_1439_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__2, &l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
v___x_1440_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1437_, v_options_1435_, v___x_1439_);
if (v___x_1440_ == 0)
{
lean_del_object(v___x_1394_);
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_Grind_updateLastTag(v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_dec_ref_known(v___x_1441_, 1);
lean_inc_ref(v_e_1248_);
v___x_1442_ = l_Lean_MessageData_ofExpr(v_e_1248_);
v___x_1443_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__4, &l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 7);
lean_ctor_set(v___x_1394_, 1, v___x_1443_);
lean_ctor_set(v___x_1394_, 0, v___x_1442_);
v___x_1445_ = v___x_1394_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_inc(v_fst_1391_);
v___x_1446_ = l_Lean_MessageData_ofExpr(v_fst_1391_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v___x_1438_, v___x_1447_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref_known(v___x_1448_, 1);
v___y_1397_ = v_a_1249_;
v___y_1398_ = v_a_1250_;
v___y_1399_ = v_a_1251_;
v___y_1400_ = v_a_1252_;
v___y_1401_ = v_a_1253_;
v___y_1402_ = v_a_1254_;
v___y_1403_ = v_a_1255_;
v___y_1404_ = v_a_1256_;
v___y_1405_ = v_a_1257_;
v___y_1406_ = v_a_1258_;
goto v___jp_1396_;
}
else
{
lean_dec(v_snd_1392_);
lean_dec(v_fst_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1248_, 3);
return v___x_1448_;
}
}
}
else
{
lean_del_object(v___x_1394_);
lean_dec(v_snd_1392_);
lean_dec(v_fst_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1248_, 3);
return v___x_1441_;
}
}
}
v___jp_1396_:
{
lean_object* v___x_1407_; 
lean_inc_ref(v_e_1248_);
v___x_1407_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1248_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
lean_inc_ref(v_e_1248_);
v___x_1409_ = l_Lean_Meta_mkOfEqTrueCore(v_e_1248_, v_a_1408_);
v___x_1410_ = l_Lean_Expr_app___override(v_snd_1392_, v___x_1409_);
v___x_1411_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1248_, v___y_1397_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
lean_inc_ref(v_e_1248_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 4);
lean_ctor_set(v___x_1389_, 0, v_e_1248_);
v___x_1414_ = v___x_1389_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_e_1248_);
v___x_1414_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_box(1);
v___x_1416_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1410_, v_fst_1391_, v_a_1412_, v___x_1414_, v___x_1415_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref_known(v___x_1416_, 1);
v___y_1318_ = v___y_1397_;
v___y_1319_ = v___y_1398_;
v___y_1320_ = v___y_1399_;
v___y_1321_ = v___y_1400_;
v___y_1322_ = v___y_1401_;
v___y_1323_ = v___y_1402_;
v___y_1324_ = v___y_1403_;
v___y_1325_ = v___y_1404_;
v___y_1326_ = v___y_1405_;
v___y_1327_ = v___y_1406_;
goto v___jp_1317_;
}
else
{
lean_dec_ref_known(v_e_1248_, 3);
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v___x_1410_);
lean_dec(v_fst_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1418_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1411_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1411_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_snd_1392_);
lean_dec(v_fst_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1426_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1407_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1407_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1386_);
v___y_1318_ = v_a_1249_;
v___y_1319_ = v_a_1250_;
v___y_1320_ = v_a_1251_;
v___y_1321_ = v_a_1252_;
v___y_1322_ = v_a_1253_;
v___y_1323_ = v_a_1254_;
v___y_1324_ = v_a_1255_;
v___y_1325_ = v_a_1256_;
v___y_1326_ = v_a_1257_;
v___y_1327_ = v_a_1258_;
goto v___jp_1317_;
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1452_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1385_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1385_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1461_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1375_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1375_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v___x_1469_; 
lean_inc_ref(v_binderType_1261_);
v___x_1469_ = l_Lean_Meta_isProp(v_binderType_1261_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; uint8_t v___x_1516_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1516_ = l_Lean_Expr_hasLooseBVars(v_body_1262_);
if (v___x_1516_ == 0)
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_unbox(v_a_1470_);
lean_dec(v_a_1470_);
if (v___x_1517_ == 0)
{
goto v___jp_1471_;
}
else
{
if (v___x_1516_ == 0)
{
lean_object* v___x_1518_; 
lean_inc_ref(v_body_1262_);
lean_inc_ref(v_binderType_1261_);
v___x_1518_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_n(v_a_1519_, 2);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__11, &l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
lean_inc_ref(v_body_1262_);
lean_inc_ref_n(v_binderType_1261_, 2);
v___x_1521_ = l_Lean_mkApp3(v___x_1520_, v_binderType_1261_, v_body_1262_, v_a_1519_);
v___x_1522_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_binderType_1261_, v___x_1521_, v_a_1249_, v_a_1251_, v_a_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref_known(v___x_1522_, 1);
v___x_1523_ = lean_obj_once(&l_Lean_Meta_Grind_propagateForallPropDown___closed__14, &l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once, _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
lean_inc_ref(v_body_1262_);
v___x_1524_ = l_Lean_mkApp3(v___x_1523_, v_binderType_1261_, v_body_1262_, v_a_1519_);
v___x_1525_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_body_1262_, v___x_1524_, v_a_1249_, v_a_1251_, v_a_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1525_;
}
else
{
lean_dec(v_a_1519_);
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
return v___x_1522_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
v_a_1526_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1518_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1518_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
goto v___jp_1471_;
}
}
}
else
{
lean_dec(v_a_1470_);
goto v___jp_1471_;
}
v___jp_1471_:
{
lean_object* v___x_1472_; 
lean_inc_ref(v_binderType_1261_);
v___x_1472_ = l_Lean_Meta_getLevel(v_binderType_1261_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1473_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
lean_inc_ref(v___x_1476_);
v___x_1477_ = l_Lean_mkConst(v___x_1474_, v___x_1476_);
lean_inc_ref(v_body_1262_);
v___x_1478_ = l_Lean_mkNot(v_body_1262_);
lean_inc_ref_n(v_binderType_1261_, 2);
lean_inc(v_binderName_1260_);
v___x_1479_ = l_Lean_mkLambda(v_binderName_1260_, v_binderInfo_1263_, v_binderType_1261_, v___x_1478_);
v___x_1480_ = l_Lean_mkAppB(v___x_1477_, v_binderType_1261_, v___x_1479_);
lean_inc_ref(v_e_1248_);
v___x_1481_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__8));
v___x_1484_ = l_Lean_mkConst(v___x_1483_, v___x_1476_);
lean_inc_ref(v_body_1262_);
lean_inc_ref_n(v_binderType_1261_, 2);
lean_inc(v_binderName_1260_);
v___x_1485_ = l_Lean_mkLambda(v_binderName_1260_, v_binderInfo_1263_, v_binderType_1261_, v_body_1262_);
v___x_1486_ = l_Lean_mkApp3(v___x_1484_, v_binderType_1261_, v___x_1485_, v_a_1482_);
v___x_1487_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1248_, v_a_1249_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_e_1248_);
v___x_1490_ = lean_box(1);
v___x_1491_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1486_, v___x_1480_, v_a_1488_, v___x_1489_, v___x_1490_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1491_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v___x_1486_);
lean_dec_ref(v___x_1480_);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1492_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1487_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1487_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v___x_1480_);
lean_dec_ref_known(v___x_1476_, 2);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1500_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1481_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1481_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1508_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1472_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1472_);
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
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1534_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1469_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1469_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
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
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1542_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1372_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1372_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
v___jp_1264_:
{
if (lean_obj_tag(v___y_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1308_; 
v_a_1276_ = lean_ctor_get(v___y_1275_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___y_1275_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1278_ = v___y_1275_;
v_isShared_1279_ = v_isSharedCheck_1308_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___y_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1308_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_unbox(v_a_1276_);
lean_dec(v_a_1276_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1281_ = lean_box(0);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v___x_1285_; 
lean_del_object(v___x_1278_);
v___x_1285_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_1248_, v___y_1266_, v___y_1274_, v___y_1273_, v___y_1270_, v___y_1267_, v___y_1269_, v___y_1271_, v___y_1265_, v___y_1272_, v___y_1268_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
lean_inc_ref(v_body_1262_);
v___x_1287_ = l_Lean_Meta_Grind_mkEqFalseProof(v_body_1262_, v___y_1266_, v___y_1274_, v___y_1273_, v___y_1270_, v___y_1267_, v___y_1269_, v___y_1271_, v___y_1265_, v___y_1272_, v___y_1268_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
lean_inc_ref(v_binderType_1261_);
v___x_1290_ = l_Lean_mkApp4(v___x_1289_, v_binderType_1261_, v_body_1262_, v_a_1286_, v_a_1288_);
v___x_1291_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_binderType_1261_, v___x_1290_, v___y_1266_, v___y_1273_, v___y_1267_, v___y_1271_, v___y_1265_, v___y_1272_, v___y_1268_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_a_1286_);
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
v_a_1292_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1287_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1287_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
v_a_1300_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1285_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1285_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1309_ = lean_ctor_get(v___y_1275_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___y_1275_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___y_1275_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___y_1275_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
v___jp_1317_:
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_Expr_hasLooseBVars(v_body_1262_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_inc_ref(v_body_1262_);
lean_inc_ref(v_binderType_1261_);
v___x_1329_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_1262_, v___y_1318_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1343_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1343_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1343_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
lean_dec_ref_known(v_e_1248_, 3);
v___x_1335_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1335_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v___x_1339_; 
lean_del_object(v___x_1332_);
lean_inc_ref(v_body_1262_);
v___x_1339_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_body_1262_, v___y_1318_, v___y_1322_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; uint8_t v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v___x_1341_ = lean_unbox(v_a_1340_);
if (v___x_1341_ == 0)
{
v___y_1265_ = v___y_1325_;
v___y_1266_ = v___y_1318_;
v___y_1267_ = v___y_1322_;
v___y_1268_ = v___y_1327_;
v___y_1269_ = v___y_1323_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1324_;
v___y_1272_ = v___y_1326_;
v___y_1273_ = v___y_1320_;
v___y_1274_ = v___y_1319_;
v___y_1275_ = v___x_1339_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref_known(v___x_1339_, 1);
lean_inc_ref(v_binderType_1261_);
v___x_1342_ = l_Lean_Meta_isProp(v_binderType_1261_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
v___y_1265_ = v___y_1325_;
v___y_1266_ = v___y_1318_;
v___y_1267_ = v___y_1322_;
v___y_1268_ = v___y_1327_;
v___y_1269_ = v___y_1323_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1324_;
v___y_1272_ = v___y_1326_;
v___y_1273_ = v___y_1320_;
v___y_1274_ = v___y_1319_;
v___y_1275_ = v___x_1342_;
goto v___jp_1264_;
}
}
else
{
v___y_1265_ = v___y_1325_;
v___y_1266_ = v___y_1318_;
v___y_1267_ = v___y_1322_;
v___y_1268_ = v___y_1327_;
v___y_1269_ = v___y_1323_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1324_;
v___y_1272_ = v___y_1326_;
v___y_1273_ = v___y_1320_;
v___y_1274_ = v___y_1319_;
v___y_1275_ = v___x_1339_;
goto v___jp_1264_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_body_1262_);
lean_dec_ref(v_binderType_1261_);
lean_dec_ref_known(v_e_1248_, 3);
v_a_1344_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1329_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1329_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v___x_1352_; 
lean_inc_ref(v_binderType_1261_);
v___x_1352_ = l_Lean_Meta_isProp(v_binderType_1261_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1363_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1363_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_unbox(v_a_1353_);
lean_dec(v_a_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_del_object(v___x_1355_);
v___x_1358_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_1248_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec_ref_known(v_e_1248_, 3);
v___x_1359_ = lean_box(0);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1359_);
v___x_1361_ = v___x_1355_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref_known(v_e_1248_, 3);
v_a_1364_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1352_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1352_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v_e_1248_);
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* v_e_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_Grind_propagateForallPropDown(v_e_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec(v_a_1553_);
return v_res_1564_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1570_ = l_Lean_mkConst(v___x_1569_, v___x_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_Lean_Expr_bvar___override(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* v_e_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1594_; 
lean_inc_ref(v_e_1579_);
v___x_1594_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1579_, v_a_1580_, v_a_1584_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1649_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1649_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1649_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_unbox(v_a_1595_);
lean_dec(v_a_1595_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec_ref(v_e_1579_);
v___x_1600_ = lean_box(0);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
lean_del_object(v___x_1597_);
lean_inc_ref(v_e_1579_);
v___x_1604_ = l_Lean_Expr_cleanupAnnotations(v_e_1579_);
v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
if (v___x_1605_ == 0)
{
lean_dec_ref(v___x_1604_);
lean_dec_ref(v_e_1579_);
goto v___jp_1591_;
}
else
{
lean_object* v_arg_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_arg_1606_ = lean_ctor_get(v___x_1604_, 1);
lean_inc_ref(v_arg_1606_);
v___x_1607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
v___x_1608_ = l_Lean_Expr_isApp(v___x_1607_);
if (v___x_1608_ == 0)
{
lean_dec_ref(v___x_1607_);
lean_dec_ref(v_arg_1606_);
lean_dec_ref(v_e_1579_);
goto v___jp_1591_;
}
else
{
lean_object* v_arg_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v_arg_1609_ = lean_ctor_get(v___x_1607_, 1);
lean_inc_ref(v_arg_1609_);
v___x_1610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1607_);
v___x_1611_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1612_ = l_Lean_Expr_isConstOf(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_dec_ref(v___x_1610_);
lean_dec_ref(v_arg_1609_);
lean_dec_ref(v_arg_1606_);
lean_dec_ref(v_e_1579_);
goto v___jp_1591_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1613_ = l_Lean_Expr_constLevels_x21(v___x_1610_);
lean_dec_ref(v___x_1610_);
v___x_1614_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__2, &l_Lean_Meta_Grind_propagateExistsDown___closed__2_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Grind_propagateExistsDown___closed__3, &l_Lean_Meta_Grind_propagateExistsDown___closed__3_once, _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
lean_inc_ref(v_arg_1606_);
v___x_1616_ = l_Lean_Expr_app___override(v_arg_1606_, v___x_1615_);
v___x_1617_ = l_Lean_Expr_headBeta(v___x_1616_);
v___x_1618_ = l_Lean_Expr_app___override(v___x_1614_, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__5));
v___x_1620_ = 0;
lean_inc_ref(v_arg_1609_);
v___x_1621_ = l_Lean_mkForall(v___x_1619_, v___x_1620_, v_arg_1609_, v___x_1618_);
lean_inc_ref(v_e_1579_);
v___x_1622_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__7));
v___x_1625_ = l_Lean_mkConst(v___x_1624_, v___x_1613_);
lean_inc_ref(v_e_1579_);
v___x_1626_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1579_, v_a_1623_);
v___x_1627_ = l_Lean_mkApp3(v___x_1625_, v_arg_1609_, v_arg_1606_, v___x_1626_);
v___x_1628_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_e_1579_);
v___x_1631_ = lean_box(1);
v___x_1632_ = l_Lean_Meta_Grind_addNewRawFact(v___x_1627_, v___x_1621_, v_a_1629_, v___x_1630_, v___x_1631_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1632_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v___x_1627_);
lean_dec_ref(v___x_1621_);
lean_dec_ref(v_e_1579_);
v_a_1633_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1628_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1628_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___x_1621_);
lean_dec(v___x_1613_);
lean_dec_ref(v_arg_1609_);
lean_dec_ref(v_arg_1606_);
lean_dec_ref(v_e_1579_);
v_a_1641_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1622_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1622_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
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
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_e_1579_);
v_a_1650_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1594_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1594_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
v___jp_1591_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Meta_Grind_propagateExistsDown(v_e_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec(v_a_1659_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_1673_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 12, 0);
v___x_1674_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9____boxed(lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_9_();
return v_res_1676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_box(0);
v___x_1684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_1685_ = l_Lean_mkConst(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* v_e_1686_){
_start:
{
if (lean_obj_tag(v_e_1686_) == 7)
{
lean_object* v_binderName_1687_; lean_object* v_binderType_1688_; lean_object* v_body_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_binderName_1687_ = lean_ctor_get(v_e_1686_, 0);
v_binderType_1688_ = lean_ctor_get(v_e_1686_, 1);
v_body_1689_ = lean_ctor_get(v_e_1686_, 2);
lean_inc_ref(v_body_1689_);
lean_inc_ref(v_binderType_1688_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_binderType_1688_);
lean_ctor_set(v___x_1690_, 1, v_body_1689_);
lean_inc(v_binderName_1687_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_binderName_1687_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Meta_Grind_propagateExistsDown___closed__1));
v___x_1694_ = lean_unsigned_to_nat(1u);
v___x_1695_ = l_Lean_Expr_isAppOfArity(v_e_1686_, v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1));
v___x_1698_ = l_Lean_Expr_appArg_x21(v_e_1686_);
v___x_1699_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4, &l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1697_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* v_e_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_e_1703_);
lean_dec_ref(v_e_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* v_fst_1705_, lean_object* v_a_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_expr_instantiate1(v_fst_1705_, v_a_1706_);
v___x_1716_ = l_Lean_Meta_getLevel(v___x_1715_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* v_fst_1717_, lean_object* v_a_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Meta_Grind_simpForall___lam__0(v_fst_1717_, v_a_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v_a_1718_);
lean_dec_ref(v_fst_1717_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1729_);
v___x_1738_ = lean_apply_9(v_k_1728_, v_b_1732_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v_b_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v_b_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* v_name_1750_, uint8_t v_bi_1751_, lean_object* v_type_1752_, lean_object* v_k_1753_, uint8_t v_kind_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___f_1763_; lean_object* v___x_1764_; 
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v___y_1755_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1763_, 0, v_k_1753_);
lean_closure_set(v___f_1763_, 1, v___y_1755_);
lean_closure_set(v___f_1763_, 2, v___y_1756_);
lean_closure_set(v___f_1763_, 3, v___y_1757_);
v___x_1764_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1750_, v_bi_1751_, v_type_1752_, v___f_1763_, v_kind_1754_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1764_) == 0)
{
return v___x_1764_;
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_1773_, lean_object* v_bi_1774_, lean_object* v_type_1775_, lean_object* v_k_1776_, lean_object* v_kind_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
uint8_t v_bi_boxed_1786_; uint8_t v_kind_boxed_1787_; lean_object* v_res_1788_; 
v_bi_boxed_1786_ = lean_unbox(v_bi_1774_);
v_kind_boxed_1787_ = lean_unbox(v_kind_1777_);
v_res_1788_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1773_, v_bi_boxed_1786_, v_type_1775_, v_k_1776_, v_kind_boxed_1787_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* v_name_1789_, lean_object* v_type_1790_, lean_object* v_k_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = 0;
v___x_1801_ = 0;
v___x_1802_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_1789_, v___x_1800_, v_type_1790_, v_k_1791_, v___x_1801_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* v_name_1803_, lean_object* v_type_1804_, lean_object* v_k_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_1803_, v_type_1804_, v_k_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__9(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = lean_box(0);
v___x_1834_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_1835_ = l_Lean_mkConst(v___x_1834_, v___x_1833_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__12(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__11));
v___x_1843_ = l_Lean_mkConst(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__15(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__14));
v___x_1851_ = l_Lean_mkConst(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__18(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__17));
v___x_1859_ = l_Lean_mkConst(v___x_1858_, v___x_1857_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__20));
v___x_1867_ = l_Lean_mkConst(v___x_1866_, v___x_1865_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_box(0);
v___x_1874_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__23));
v___x_1875_ = l_Lean_mkConst(v___x_1874_, v___x_1873_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__26));
v___x_1882_ = l_Lean_mkConst(v___x_1881_, v___x_1880_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__29));
v___x_1890_ = l_Lean_mkConst(v___x_1889_, v___x_1888_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__31(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = l_Lean_Level_ofNat(v___x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__32(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__31, &l_Lean_Meta_Grind_simpForall___closed__31_once, _init_l_Lean_Meta_Grind_simpForall___closed__31);
v___x_1894_ = l_Lean_mkSort(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__35(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__34));
v___x_1900_ = l_Lean_mkConst(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* v_e_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; 
if (lean_obj_tag(v_e_1901_) == 7)
{
lean_object* v_binderName_1952_; lean_object* v_binderType_1953_; lean_object* v_body_1954_; uint8_t v_binderInfo_1955_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; uint8_t v___x_2130_; 
v_binderName_1952_ = lean_ctor_get(v_e_1901_, 0);
v_binderType_1953_ = lean_ctor_get(v_e_1901_, 1);
v_body_1954_ = lean_ctor_get(v_e_1901_, 2);
v_binderInfo_1955_ = lean_ctor_get_uint8(v_e_1901_, sizeof(void*)*3 + 8);
v___x_2130_ = l_Lean_Expr_hasLooseBVars(v_body_1954_);
if (v___x_2130_ == 0)
{
uint8_t v___x_2131_; lean_object* v___y_2133_; lean_object* v___x_2157_; 
v___x_2131_ = 1;
lean_inc_ref(v_binderType_1953_);
v___x_2157_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1953_, v_a_1906_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = l_Lean_Expr_cleanupAnnotations(v_a_2158_);
v___x_2160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2161_ = l_Lean_Expr_isConstOf(v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2163_ = l_Lean_Expr_isConstOf(v___x_2159_, v___x_2162_);
lean_dec_ref(v___x_2159_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_inc_ref(v_body_1954_);
v___x_2164_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_1954_, v_a_1906_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = l_Lean_Expr_cleanupAnnotations(v_a_2165_);
v___x_2167_ = l_Lean_Expr_isConstOf(v___x_2166_, v___x_2160_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Lean_Expr_isConstOf(v___x_2166_, v___x_2162_);
lean_dec_ref(v___x_2166_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_inc_ref(v_binderType_1953_);
v___x_2169_ = l_Lean_Meta_isProp(v_binderType_1953_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v___x_2171_ = lean_unbox(v_a_2170_);
if (v___x_2171_ == 0)
{
v___y_2133_ = v___x_2169_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2172_; 
lean_dec_ref_known(v___x_2169_, 1);
lean_inc_ref(v_body_1954_);
lean_inc_ref(v_binderType_1953_);
v___x_2172_ = l_Lean_Meta_isExprDefEq(v_binderType_1953_, v_body_1954_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
v___y_2133_ = v___x_2172_;
goto v___jp_2132_;
}
}
else
{
v___y_2133_ = v___x_2169_;
goto v___jp_2132_;
}
}
else
{
lean_object* v___x_2173_; 
lean_inc_ref(v_binderType_1953_);
v___x_2173_ = l_Lean_Meta_isProp(v_binderType_1953_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2188_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2188_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2188_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_unbox(v_a_2174_);
lean_dec(v_a_2174_);
if (v___x_2178_ == 0)
{
lean_del_object(v___x_2176_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_inc_ref(v_binderType_1953_);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2179_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2180_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__15, &l_Lean_Meta_Grind_simpForall___closed__15_once, _init_l_Lean_Meta_Grind_simpForall___closed__15);
v___x_2181_ = l_Lean_Expr_app___override(v___x_2180_, v_binderType_1953_);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2183_, 0, v___x_2179_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*2, v___x_2131_);
v___x_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2184_);
v___x_2186_ = v___x_2176_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref_known(v_e_1901_, 3);
v_a_2189_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2173_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2173_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
else
{
lean_object* v___x_2197_; 
lean_dec_ref(v___x_2166_);
lean_inc_ref(v_binderType_1953_);
v___x_2197_ = l_Lean_Meta_isProp(v_binderType_1953_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2212_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_unbox(v_a_2198_);
lean_dec(v_a_2198_);
if (v___x_2202_ == 0)
{
lean_del_object(v___x_2200_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_inc_ref_n(v_binderType_1953_, 2);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2203_ = l_Lean_mkNot(v_binderType_1953_);
v___x_2204_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__18, &l_Lean_Meta_Grind_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_simpForall___closed__18);
v___x_2205_ = l_Lean_Expr_app___override(v___x_2204_, v_binderType_1953_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2203_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*2, v___x_2131_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2208_);
v___x_2210_ = v___x_2200_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref_known(v_e_1901_, 3);
v_a_2213_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2197_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2197_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref_known(v_e_1901_, 3);
v_a_2221_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2164_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2164_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v___x_2229_; 
lean_inc_ref(v_body_1954_);
v___x_2229_ = l_Lean_Meta_isProp(v_body_1954_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2243_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2243_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
if (v___x_2234_ == 0)
{
lean_del_object(v___x_2232_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_inc_ref_n(v_body_1954_, 2);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2235_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__21, &l_Lean_Meta_Grind_simpForall___closed__21_once, _init_l_Lean_Meta_Grind_simpForall___closed__21);
v___x_2236_ = l_Lean_Expr_app___override(v___x_2235_, v_body_1954_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2238_, 0, v_body_1954_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*2, v___x_2131_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2239_);
v___x_2241_ = v___x_2232_;
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
lean_dec_ref_known(v_e_1901_, 3);
v_a_2244_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2229_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2229_);
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
lean_dec_ref(v___x_2159_);
lean_inc_ref(v_body_1954_);
v___x_2252_ = l_Lean_Meta_isProp(v_body_1954_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
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
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_inc_ref(v_body_1954_);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2258_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2259_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__24, &l_Lean_Meta_Grind_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_simpForall___closed__24);
v___x_2260_ = l_Lean_Expr_app___override(v___x_2259_, v_body_1954_);
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2262_, 0, v___x_2258_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*2, v___x_2131_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
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
lean_dec_ref_known(v_e_1901_, 3);
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
lean_dec_ref_known(v_e_1901_, 3);
v_a_2276_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2157_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2157_);
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
v___jp_2132_:
{
if (lean_obj_tag(v___y_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2148_; 
v_a_2134_ = lean_ctor_get(v___y_2133_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___y_2133_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2136_ = v___y_2133_;
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___y_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2148_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_unbox(v_a_2134_);
lean_dec(v_a_2134_);
if (v___x_2138_ == 0)
{
lean_del_object(v___x_2136_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_inc_ref(v_binderType_1953_);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2139_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2140_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__12, &l_Lean_Meta_Grind_simpForall___closed__12_once, _init_l_Lean_Meta_Grind_simpForall___closed__12);
v___x_2141_ = l_Lean_Expr_app___override(v___x_2140_, v_binderType_1953_);
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2143_, 0, v___x_2139_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*2, v___x_2131_);
v___x_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2144_);
v___x_2146_ = v___x_2136_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref_known(v_e_1901_, 3);
v_a_2149_ = lean_ctor_get(v___y_2133_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___y_2133_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___y_2133_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___y_2133_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
else
{
lean_object* v___x_2284_; 
lean_inc_ref(v_binderType_1953_);
v___x_2284_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_1953_, v_a_1906_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = l_Lean_Expr_cleanupAnnotations(v_a_2285_);
v___x_2287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3));
v___x_2288_ = l_Lean_Expr_isConstOf(v___x_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__8));
v___x_2290_ = l_Lean_Expr_isConstOf(v___x_2286_, v___x_2289_);
lean_dec_ref(v___x_2286_);
if (v___x_2290_ == 0)
{
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__27, &l_Lean_Meta_Grind_simpForall___closed__27_once, _init_l_Lean_Meta_Grind_simpForall___closed__27);
v___x_2292_ = lean_expr_instantiate1(v_body_1954_, v___x_2291_);
lean_inc_ref(v___x_2292_);
v___x_2293_ = l_Lean_Meta_isProp(v___x_2292_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2308_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_unbox(v_a_2294_);
lean_dec(v_a_2294_);
if (v___x_2298_ == 0)
{
lean_del_object(v___x_2296_);
lean_dec_ref(v___x_2292_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_inc_ref(v_body_1954_);
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2299_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_body_1954_);
v___x_2300_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__30, &l_Lean_Meta_Grind_simpForall___closed__30_once, _init_l_Lean_Meta_Grind_simpForall___closed__30);
v___x_2301_ = l_Lean_Expr_app___override(v___x_2300_, v___x_2299_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2303_, 0, v___x_2292_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*2, v___x_2130_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2304_);
v___x_2306_ = v___x_2296_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_2292_);
lean_dec_ref_known(v_e_1901_, 3);
v_a_2309_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2293_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2293_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v___x_2286_);
lean_inc_ref(v_body_1954_);
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
v___x_2317_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_body_1954_);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc_ref(v___x_2317_);
v___x_2318_ = lean_infer_type(v___x_2317_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__32, &l_Lean_Meta_Grind_simpForall___closed__32_once, _init_l_Lean_Meta_Grind_simpForall___closed__32);
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
v___x_2321_ = l_Lean_mkForall(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v___x_2320_);
v___x_2322_ = l_Lean_Meta_isExprDefEq(v_a_2319_, v___x_2321_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2337_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2337_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
uint8_t v___x_2327_; 
v___x_2327_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
if (v___x_2327_ == 0)
{
lean_del_object(v___x_2325_);
lean_dec_ref(v___x_2317_);
v___y_2119_ = v_a_1902_;
v___y_2120_ = v_a_1903_;
v___y_2121_ = v_a_1904_;
v___y_2122_ = v_a_1905_;
v___y_2123_ = v_a_1906_;
v___y_2124_ = v_a_1907_;
v___y_2125_ = v_a_1908_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
lean_dec_ref_known(v_e_1901_, 3);
v___x_2328_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__9, &l_Lean_Meta_Grind_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_simpForall___closed__9);
v___x_2329_ = lean_obj_once(&l_Lean_Meta_Grind_simpForall___closed__35, &l_Lean_Meta_Grind_simpForall___closed__35_once, _init_l_Lean_Meta_Grind_simpForall___closed__35);
v___x_2330_ = l_Lean_Expr_app___override(v___x_2329_, v___x_2317_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2328_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*2, v___x_2130_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2333_);
v___x_2335_ = v___x_2325_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref_known(v_e_1901_, 3);
v_a_2338_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2322_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2322_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref_known(v_e_1901_, 3);
v_a_2346_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2318_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2318_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref_known(v_e_1901_, 3);
v_a_2354_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2284_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2284_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
v___jp_1956_:
{
if (v___y_1964_ == 0)
{
v___y_1911_ = v___y_1961_;
v___y_1912_ = v___y_1963_;
v___y_1913_ = v___y_1958_;
v___y_1914_ = v___y_1960_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = l_Lean_Expr_appFn_x21(v_body_1954_);
v___x_1966_ = l_Lean_Expr_appFn_x21(v___x_1965_);
if (lean_obj_tag(v___x_1966_) == 4)
{
lean_object* v_declName_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_declName_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_declName_1967_);
lean_dec_ref_known(v___x_1966_, 2);
v___x_1968_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_1969_ = lean_name_eq(v_declName_1967_, v___x_1968_);
lean_dec(v_declName_1967_);
if (v___x_1969_ == 0)
{
lean_dec_ref(v___x_1965_);
v___y_1911_ = v___y_1961_;
v___y_1912_ = v___y_1963_;
v___y_1913_ = v___y_1958_;
v___y_1914_ = v___y_1960_;
goto v___jp_1910_;
}
else
{
lean_object* v_pRaw_1970_; lean_object* v_pRaw_1971_; lean_object* v___x_1972_; 
v_pRaw_1970_ = l_Lean_Expr_appArg_x21(v___x_1965_);
lean_dec_ref(v___x_1965_);
v_pRaw_1971_ = l_Lean_Expr_appArg_x21(v_body_1954_);
v___x_1972_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1970_);
if (lean_obj_tag(v___x_1972_) == 1)
{
lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2043_; 
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
lean_dec_ref(v_pRaw_1970_);
lean_dec_ref_known(v_e_1901_, 3);
v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2043_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2043_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_snd_1977_; lean_object* v_fst_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2042_; 
v_snd_1977_ = lean_ctor_get(v_val_1973_, 1);
v_fst_1978_ = lean_ctor_get(v_val_1973_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_val_1973_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_1980_ = v_val_1973_;
v_isShared_1981_ = v_isSharedCheck_2042_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_snd_1977_);
lean_inc(v_fst_1978_);
lean_dec(v_val_1973_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2042_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2041_; 
v_fst_1982_ = lean_ctor_get(v_snd_1977_, 0);
v_snd_1983_ = lean_ctor_get(v_snd_1977_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_snd_1977_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1985_ = v_snd_1977_;
v_isShared_1986_ = v_isSharedCheck_2041_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_dec(v_snd_1977_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2041_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___f_1987_; lean_object* v_p_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v_q_1991_; lean_object* v_00_u03b2_1992_; lean_object* v___x_1993_; 
lean_inc_n(v_fst_1982_, 3);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1987_, 0, v_fst_1982_);
lean_inc_ref(v_pRaw_1971_);
lean_inc_ref_n(v_binderType_1953_, 4);
lean_inc_n(v_binderName_1952_, 3);
v_p_1988_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_pRaw_1971_);
v___x_1989_ = 0;
lean_inc(v_snd_1983_);
lean_inc(v_fst_1978_);
v___x_1990_ = l_Lean_mkLambda(v_fst_1978_, v___x_1989_, v_fst_1982_, v_snd_1983_);
v_q_1991_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v___x_1990_);
v_00_u03b2_1992_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_fst_1982_);
v___x_1993_ = l_Lean_Meta_getLevel(v_binderType_1953_, v___y_1961_, v___y_1963_, v___y_1958_, v___y_1960_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
v___x_1995_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1952_, v_binderType_1953_, v___f_1987_, v___y_1959_, v___y_1962_, v___y_1957_, v___y_1961_, v___y_1963_, v___y_1958_, v___y_1960_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2024_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2024_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2024_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_expr_lift_loose_bvars(v_pRaw_1971_, v___x_2000_, v___x_2001_);
lean_dec_ref(v_pRaw_1971_);
v___x_2003_ = l_Lean_mkOr(v_snd_1983_, v___x_2002_);
v___x_2004_ = l_Lean_mkForall(v_fst_1978_, v___x_1989_, v_fst_1982_, v___x_2003_);
lean_inc_ref(v_binderType_1953_);
v___x_2005_ = l_Lean_mkForall(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__4));
v___x_2007_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 1, v___x_2007_);
lean_ctor_set(v___x_1985_, 0, v_a_1996_);
v___x_2009_ = v___x_1985_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_1996_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 1, v___x_2009_);
lean_ctor_set(v___x_1980_, 0, v_a_1994_);
v___x_2011_ = v___x_1980_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_1994_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2012_ = l_Lean_mkConst(v___x_2006_, v___x_2011_);
v___x_2013_ = l_Lean_mkApp4(v___x_2012_, v_binderType_1953_, v_00_u03b2_1992_, v_p_1988_, v_q_1991_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_2013_);
v___x_2015_ = v___x_1975_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2016_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2016_, 0, v___x_2005_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*2, v___x_1969_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2017_);
v___x_2019_ = v___x_1998_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1994_);
lean_dec_ref(v_00_u03b2_1992_);
lean_dec_ref(v_q_1991_);
lean_dec_ref(v_p_1988_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1975_);
lean_dec_ref(v_pRaw_1971_);
lean_dec_ref(v_binderType_1953_);
lean_dec(v_binderName_1952_);
v_a_2025_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1995_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1995_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v_00_u03b2_1992_);
lean_dec_ref(v_q_1991_);
lean_dec_ref(v_p_1988_);
lean_dec_ref(v___f_1987_);
lean_del_object(v___x_1985_);
lean_dec(v_snd_1983_);
lean_dec(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_fst_1978_);
lean_del_object(v___x_1975_);
lean_dec_ref(v_pRaw_1971_);
lean_dec_ref(v_binderType_1953_);
lean_dec(v_binderName_1952_);
v_a_2033_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1993_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1993_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v___x_1972_);
v___x_2044_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_1971_);
lean_dec_ref(v_pRaw_1971_);
if (lean_obj_tag(v___x_2044_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2115_; 
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
lean_dec_ref_known(v_e_1901_, 3);
v_val_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2115_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_val_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2115_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_snd_2049_; lean_object* v_fst_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2114_; 
v_snd_2049_ = lean_ctor_get(v_val_2045_, 1);
v_fst_2050_ = lean_ctor_get(v_val_2045_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_val_2045_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2052_ = v_val_2045_;
v_isShared_2053_ = v_isSharedCheck_2114_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_snd_2049_);
lean_inc(v_fst_2050_);
lean_dec(v_val_2045_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2114_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2113_; 
v_fst_2054_ = lean_ctor_get(v_snd_2049_, 0);
v_snd_2055_ = lean_ctor_get(v_snd_2049_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_snd_2049_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2057_ = v_snd_2049_;
v_isShared_2058_ = v_isSharedCheck_2113_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
lean_dec(v_snd_2049_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2113_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___f_2059_; lean_object* v_p_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v_q_2063_; lean_object* v_00_u03b2_2064_; lean_object* v___x_2065_; 
lean_inc_n(v_fst_2054_, 3);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2059_, 0, v_fst_2054_);
lean_inc_ref(v_pRaw_1970_);
lean_inc_ref_n(v_binderType_1953_, 4);
lean_inc_n(v_binderName_1952_, 3);
v_p_2060_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_pRaw_1970_);
v___x_2061_ = 0;
lean_inc(v_snd_2055_);
lean_inc(v_fst_2050_);
v___x_2062_ = l_Lean_mkLambda(v_fst_2050_, v___x_2061_, v_fst_2054_, v_snd_2055_);
v_q_2063_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v___x_2062_);
v_00_u03b2_2064_ = l_Lean_mkLambda(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v_fst_2054_);
v___x_2065_ = l_Lean_Meta_getLevel(v_binderType_1953_, v___y_1961_, v___y_1963_, v___y_1958_, v___y_1960_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
lean_inc_ref(v_binderType_1953_);
lean_inc(v_binderName_1952_);
v___x_2067_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_1952_, v_binderType_1953_, v___f_2059_, v___y_1959_, v___y_1962_, v___y_1957_, v___y_1961_, v___y_1963_, v___y_1958_, v___y_1960_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2096_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2096_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2096_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_unsigned_to_nat(1u);
v___x_2074_ = lean_expr_lift_loose_bvars(v_pRaw_1970_, v___x_2072_, v___x_2073_);
lean_dec_ref(v_pRaw_1970_);
v___x_2075_ = l_Lean_mkOr(v___x_2074_, v_snd_2055_);
v___x_2076_ = l_Lean_mkForall(v_fst_2050_, v___x_2061_, v_fst_2054_, v___x_2075_);
lean_inc_ref(v_binderType_1953_);
v___x_2077_ = l_Lean_mkForall(v_binderName_1952_, v_binderInfo_1955_, v_binderType_1953_, v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__6));
v___x_2079_ = lean_box(0);
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 1, v___x_2079_);
lean_ctor_set(v___x_2057_, 0, v_a_2068_);
v___x_2081_ = v___x_2057_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2068_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
lean_ctor_set(v___x_2052_, 1, v___x_2081_);
lean_ctor_set(v___x_2052_, 0, v_a_2066_);
v___x_2083_ = v___x_2052_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2066_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2084_ = l_Lean_mkConst(v___x_2078_, v___x_2083_);
v___x_2085_ = l_Lean_mkApp4(v___x_2084_, v_binderType_1953_, v_00_u03b2_2064_, v_p_2060_, v_q_2063_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2085_);
v___x_2087_ = v___x_2047_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2088_, 0, v___x_2077_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*2, v___x_1969_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2089_);
v___x_2091_ = v___x_2070_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
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
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2066_);
lean_dec_ref(v_00_u03b2_2064_);
lean_dec_ref(v_q_2063_);
lean_dec_ref(v_p_2060_);
lean_del_object(v___x_2057_);
lean_dec(v_snd_2055_);
lean_dec(v_fst_2054_);
lean_del_object(v___x_2052_);
lean_dec(v_fst_2050_);
lean_del_object(v___x_2047_);
lean_dec_ref(v_pRaw_1970_);
lean_dec_ref(v_binderType_1953_);
lean_dec(v_binderName_1952_);
v_a_2097_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2067_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2067_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_00_u03b2_2064_);
lean_dec_ref(v_q_2063_);
lean_dec_ref(v_p_2060_);
lean_dec_ref(v___f_2059_);
lean_del_object(v___x_2057_);
lean_dec(v_snd_2055_);
lean_dec(v_fst_2054_);
lean_del_object(v___x_2052_);
lean_dec(v_fst_2050_);
lean_del_object(v___x_2047_);
lean_dec_ref(v_pRaw_1970_);
lean_dec_ref(v_binderType_1953_);
lean_dec(v_binderName_1952_);
v_a_2105_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2065_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2065_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2044_);
lean_dec_ref(v_pRaw_1970_);
v___y_1911_ = v___y_1961_;
v___y_1912_ = v___y_1963_;
v___y_1913_ = v___y_1958_;
v___y_1914_ = v___y_1960_;
goto v___jp_1910_;
}
}
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref(v___x_1966_);
lean_dec_ref(v___x_1965_);
lean_dec_ref_known(v_e_1901_, 3);
v___x_2116_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
}
v___jp_2118_:
{
uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_Expr_isApp(v_body_1954_);
if (v___x_2126_ == 0)
{
v___y_1957_ = v___y_2121_;
v___y_1958_ = v___y_2124_;
v___y_1959_ = v___y_2119_;
v___y_1960_ = v___y_2125_;
v___y_1961_ = v___y_2122_;
v___y_1962_ = v___y_2120_;
v___y_1963_ = v___y_2123_;
v___y_1964_ = v___x_2126_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = l_Lean_Expr_getAppNumArgs(v_body_1954_);
v___x_2128_ = lean_unsigned_to_nat(2u);
v___x_2129_ = lean_nat_dec_eq(v___x_2127_, v___x_2128_);
lean_dec(v___x_2127_);
v___y_1957_ = v___y_2121_;
v___y_1958_ = v___y_2124_;
v___y_1959_ = v___y_2119_;
v___y_1960_ = v___y_2125_;
v___y_1961_ = v___y_2122_;
v___y_1962_ = v___y_2120_;
v___y_1963_ = v___y_2123_;
v___y_1964_ = v___x_2129_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref(v_e_1901_);
v___x_2362_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
v___jp_1910_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_1901_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1943_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1943_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1943_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
if (lean_obj_tag(v_a_1916_) == 1)
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1938_; 
v_val_1920_ = lean_ctor_get(v_a_1916_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_a_1916_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1922_ = v_a_1916_;
v_isShared_1923_ = v_isSharedCheck_1938_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v_a_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1938_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_snd_1924_; lean_object* v_fst_1925_; lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v_snd_1924_ = lean_ctor_get(v_val_1920_, 1);
lean_inc(v_snd_1924_);
v_fst_1925_ = lean_ctor_get(v_val_1920_, 0);
lean_inc(v_fst_1925_);
lean_dec(v_val_1920_);
v_fst_1926_ = lean_ctor_get(v_snd_1924_, 0);
lean_inc(v_fst_1926_);
v_snd_1927_ = lean_ctor_get(v_snd_1924_, 1);
lean_inc(v_snd_1927_);
lean_dec(v_snd_1924_);
v___x_1928_ = l_Lean_mkAnd(v_fst_1925_, v_fst_1926_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_snd_1927_);
v___x_1930_ = v___x_1922_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_snd_1927_);
v___x_1930_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1931_ = 1;
v___x_1932_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1932_, 0, v___x_1928_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*2, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1933_);
v___x_1935_ = v___x_1918_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec(v_a_1916_);
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1939_);
v___x_1941_ = v___x_1918_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1915_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1915_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* v_e_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_Meta_Grind_simpForall(v_e_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* v_00_u03b1_2374_, lean_object* v_name_2375_, uint8_t v_bi_2376_, lean_object* v_type_2377_, lean_object* v_k_2378_, uint8_t v_kind_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_2375_, v_bi_2376_, v_type_2377_, v_k_2378_, v_kind_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_name_2390_, lean_object* v_bi_2391_, lean_object* v_type_2392_, lean_object* v_k_2393_, lean_object* v_kind_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_bi_boxed_2403_; uint8_t v_kind_boxed_2404_; lean_object* v_res_2405_; 
v_bi_boxed_2403_ = lean_unbox(v_bi_2391_);
v_kind_boxed_2404_ = lean_unbox(v_kind_2394_);
v_res_2405_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_2389_, v_name_2390_, v_bi_boxed_2403_, v_type_2392_, v_k_2393_, v_kind_boxed_2404_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* v_00_u03b1_2406_, lean_object* v_name_2407_, lean_object* v_type_2408_, lean_object* v_k_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_name_2407_, v_type_2408_, v_k_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_name_2420_, lean_object* v_type_2421_, lean_object* v_k_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(v_00_u03b1_2419_, v_name_2420_, v_type_2421_, v_k_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_));
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_));
v___x_2448_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
v___x_2449_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2446_, v___x_2447_, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12____boxed(lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_();
return v_res_2451_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__5));
v___x_2467_ = l_Lean_mkConst(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* v_e_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = l_Lean_Expr_cleanupAnnotations(v_e_2486_);
v___x_2499_ = l_Lean_Expr_isApp(v___x_2498_);
if (v___x_2499_ == 0)
{
lean_dec_ref(v___x_2498_);
goto v___jp_2492_;
}
else
{
lean_object* v_arg_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v_arg_2500_ = lean_ctor_get(v___x_2498_, 1);
lean_inc_ref(v_arg_2500_);
v___x_2501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2498_);
v___x_2502_ = l_Lean_Expr_isApp(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v___x_2501_);
lean_dec_ref(v_arg_2500_);
goto v___jp_2492_;
}
else
{
lean_object* v_arg_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_arg_2503_ = lean_ctor_get(v___x_2501_, 1);
lean_inc_ref(v_arg_2503_);
v___x_2504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2501_);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Grind_propagateForallPropDown___closed__6));
v___x_2506_ = l_Lean_Expr_isConstOf(v___x_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
lean_dec_ref(v_arg_2500_);
goto v___jp_2492_;
}
else
{
if (lean_obj_tag(v_arg_2500_) == 6)
{
lean_object* v_binderName_2507_; lean_object* v_body_2508_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; uint8_t v___y_2577_; uint8_t v___y_2604_; uint8_t v___x_2633_; 
v_binderName_2507_ = lean_ctor_get(v_arg_2500_, 0);
lean_inc(v_binderName_2507_);
v_body_2508_ = lean_ctor_get(v_arg_2500_, 2);
lean_inc_ref(v_body_2508_);
lean_dec_ref_known(v_arg_2500_, 3);
v___x_2633_ = l_Lean_Expr_isApp(v_body_2508_);
if (v___x_2633_ == 0)
{
v___y_2604_ = v___x_2633_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2634_ = l_Lean_Expr_getAppNumArgs(v_body_2508_);
v___x_2635_ = lean_unsigned_to_nat(2u);
v___x_2636_ = lean_nat_dec_eq(v___x_2634_, v___x_2635_);
lean_dec(v___x_2634_);
v___y_2604_ = v___x_2636_;
goto v___jp_2603_;
}
v___jp_2509_:
{
uint8_t v___x_2514_; 
v___x_2514_ = l_Lean_Expr_hasLooseBVars(v_body_2508_);
if (v___x_2514_ == 0)
{
if (v___x_2506_ == 0)
{
lean_dec_ref(v_body_2508_);
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
goto v___jp_2495_;
}
else
{
lean_object* v___x_2515_; 
lean_inc_ref(v_arg_2503_);
v___x_2515_ = l_Lean_Meta_isProp(v_arg_2503_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2564_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2564_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2564_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2518_);
v___x_2521_ = l_Lean_Expr_constLevels_x21(v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2522_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__1));
lean_inc(v___x_2521_);
v___x_2523_ = l_Lean_mkConst(v___x_2522_, v___x_2521_);
lean_inc_ref(v_arg_2503_);
v___x_2524_ = l_Lean_Expr_app___override(v___x_2523_, v_arg_2503_);
v___x_2525_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_2524_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2546_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2546_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2546_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
if (lean_obj_tag(v_a_2526_) == 1)
{
lean_object* v_val_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2545_; 
v_val_2530_ = lean_ctor_get(v_a_2526_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_a_2526_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2532_ = v_a_2526_;
v_isShared_2533_ = v_isSharedCheck_2545_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_val_2530_);
lean_dec(v_a_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2545_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2534_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__3));
v___x_2535_ = l_Lean_mkConst(v___x_2534_, v___x_2521_);
lean_inc_ref(v_body_2508_);
v___x_2536_ = l_Lean_mkApp3(v___x_2535_, v_arg_2503_, v_val_2530_, v_body_2508_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2536_);
v___x_2538_ = v___x_2532_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2539_, 0, v_body_2508_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*2, v___x_2506_);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2540_);
v___x_2542_ = v___x_2528_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_del_object(v___x_2528_);
lean_dec(v_a_2526_);
lean_dec(v___x_2521_);
lean_dec_ref(v_body_2508_);
lean_dec_ref(v_arg_2503_);
goto v___jp_2495_;
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v___x_2521_);
lean_dec_ref(v_body_2508_);
lean_dec_ref(v_arg_2503_);
v_a_2547_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2525_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2525_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec_ref(v___x_2504_);
lean_inc_ref(v_body_2508_);
lean_inc_ref(v_arg_2503_);
v___x_2555_ = l_Lean_mkAnd(v_arg_2503_, v_body_2508_);
v___x_2556_ = lean_obj_once(&l_Lean_Meta_Grind_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6);
v___x_2557_ = l_Lean_mkAppB(v___x_2556_, v_arg_2503_, v_body_2508_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2555_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*2, v___x_2506_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2560_);
v___x_2562_ = v___x_2518_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_body_2508_);
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
v_a_2565_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2515_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2515_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
else
{
lean_dec_ref(v_body_2508_);
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
goto v___jp_2495_;
}
}
v___jp_2573_:
{
if (v___y_2577_ == 0)
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Lean_Expr_hasLooseBVars(v___y_2574_);
if (v___x_2578_ == 0)
{
if (v___y_2576_ == 0)
{
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v_binderName_2507_);
v___y_2510_ = v_a_2487_;
v___y_2511_ = v_a_2488_;
v___y_2512_ = v_a_2489_;
v___y_2513_ = v_a_2490_;
goto v___jp_2509_;
}
else
{
uint8_t v___x_2579_; lean_object* v_p_2580_; lean_object* v___x_2581_; lean_object* v_expr_2582_; lean_object* v_u_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref(v_body_2508_);
v___x_2579_ = 0;
lean_inc_ref_n(v_arg_2503_, 2);
v_p_2580_ = l_Lean_mkLambda(v_binderName_2507_, v___x_2579_, v_arg_2503_, v___y_2575_);
lean_inc_ref(v_p_2580_);
lean_inc_ref(v___x_2504_);
v___x_2581_ = l_Lean_mkAppB(v___x_2504_, v_arg_2503_, v_p_2580_);
lean_inc_ref(v___y_2574_);
v_expr_2582_ = l_Lean_mkAnd(v___x_2581_, v___y_2574_);
v_u_2583_ = l_Lean_Expr_constLevels_x21(v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2584_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__8));
v___x_2585_ = l_Lean_mkConst(v___x_2584_, v_u_2583_);
v___x_2586_ = l_Lean_mkApp3(v___x_2585_, v_arg_2503_, v_p_2580_, v___y_2574_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2588_, 0, v_expr_2582_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*2, v___x_2506_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
else
{
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v_binderName_2507_);
v___y_2510_ = v_a_2487_;
v___y_2511_ = v_a_2488_;
v___y_2512_ = v_a_2489_;
v___y_2513_ = v_a_2490_;
goto v___jp_2509_;
}
}
else
{
uint8_t v___x_2591_; lean_object* v_p_2592_; lean_object* v___x_2593_; lean_object* v_expr_2594_; lean_object* v_u_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_dec_ref(v_body_2508_);
v___x_2591_ = 0;
lean_inc_ref_n(v_arg_2503_, 2);
v_p_2592_ = l_Lean_mkLambda(v_binderName_2507_, v___x_2591_, v_arg_2503_, v___y_2574_);
lean_inc_ref(v_p_2592_);
lean_inc_ref(v___x_2504_);
v___x_2593_ = l_Lean_mkAppB(v___x_2504_, v_arg_2503_, v_p_2592_);
lean_inc_ref(v___y_2575_);
v_expr_2594_ = l_Lean_mkAnd(v___y_2575_, v___x_2593_);
v_u_2595_ = l_Lean_Expr_constLevels_x21(v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2596_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__10));
v___x_2597_ = l_Lean_mkConst(v___x_2596_, v_u_2595_);
v___x_2598_ = l_Lean_mkApp3(v___x_2597_, v_arg_2503_, v_p_2592_, v___y_2575_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2600_, 0, v_expr_2594_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*2, v___x_2506_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
v___jp_2603_:
{
if (v___y_2604_ == 0)
{
lean_dec(v_binderName_2507_);
v___y_2510_ = v_a_2487_;
v___y_2511_ = v_a_2488_;
v___y_2512_ = v_a_2489_;
v___y_2513_ = v_a_2490_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = l_Lean_Expr_appFn_x21(v_body_2508_);
v___x_2606_ = l_Lean_Expr_appFn_x21(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 4)
{
lean_object* v_declName_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v_declName_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_declName_2607_);
lean_dec_ref_known(v___x_2606_, 2);
v___x_2608_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__2));
v___x_2609_ = lean_name_eq(v_declName_2607_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__12));
v___x_2611_ = lean_name_eq(v_declName_2607_, v___x_2610_);
lean_dec(v_declName_2607_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v___x_2605_);
lean_dec(v_binderName_2507_);
v___y_2510_ = v_a_2487_;
v___y_2511_ = v_a_2488_;
v___y_2512_ = v_a_2489_;
v___y_2513_ = v_a_2490_;
goto v___jp_2509_;
}
else
{
lean_object* v_b_2612_; lean_object* v_b_2613_; uint8_t v___x_2614_; 
v_b_2612_ = l_Lean_Expr_appArg_x21(v___x_2605_);
lean_dec_ref(v___x_2605_);
v_b_2613_ = l_Lean_Expr_appArg_x21(v_body_2508_);
v___x_2614_ = l_Lean_Expr_hasLooseBVars(v_b_2612_);
if (v___x_2614_ == 0)
{
v___y_2574_ = v_b_2613_;
v___y_2575_ = v_b_2612_;
v___y_2576_ = v___x_2611_;
v___y_2577_ = v___x_2611_;
goto v___jp_2573_;
}
else
{
v___y_2574_ = v_b_2613_;
v___y_2575_ = v_b_2612_;
v___y_2576_ = v___x_2611_;
v___y_2577_ = v___x_2609_;
goto v___jp_2573_;
}
}
}
else
{
lean_object* v_pRaw_2615_; lean_object* v_qRaw_2616_; uint8_t v___x_2617_; lean_object* v_p_2618_; lean_object* v_q_2619_; lean_object* v_u_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_expr_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_declName_2607_);
v_pRaw_2615_ = l_Lean_Expr_appArg_x21(v___x_2605_);
lean_dec_ref(v___x_2605_);
v_qRaw_2616_ = l_Lean_Expr_appArg_x21(v_body_2508_);
lean_dec_ref(v_body_2508_);
v___x_2617_ = 0;
lean_inc_ref_n(v_arg_2503_, 4);
lean_inc(v_binderName_2507_);
v_p_2618_ = l_Lean_mkLambda(v_binderName_2507_, v___x_2617_, v_arg_2503_, v_pRaw_2615_);
v_q_2619_ = l_Lean_mkLambda(v_binderName_2507_, v___x_2617_, v_arg_2503_, v_qRaw_2616_);
v_u_2620_ = l_Lean_Expr_constLevels_x21(v___x_2504_);
lean_inc_ref(v_p_2618_);
lean_inc_ref(v___x_2504_);
v___x_2621_ = l_Lean_mkAppB(v___x_2504_, v_arg_2503_, v_p_2618_);
lean_inc_ref(v_q_2619_);
v___x_2622_ = l_Lean_mkAppB(v___x_2504_, v_arg_2503_, v_q_2619_);
v_expr_2623_ = l_Lean_mkOr(v___x_2621_, v___x_2622_);
v___x_2624_ = ((lean_object*)(l_Lean_Meta_Grind_simpExists___redArg___closed__14));
v___x_2625_ = l_Lean_mkConst(v___x_2624_, v_u_2620_);
v___x_2626_ = l_Lean_mkApp3(v___x_2625_, v_arg_2503_, v_p_2618_, v_q_2619_);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2628_, 0, v_expr_2623_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*2, v___x_2506_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v___x_2606_);
lean_dec_ref(v___x_2605_);
lean_dec_ref(v_body_2508_);
lean_dec(v_binderName_2507_);
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
v___x_2631_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec_ref(v___x_2504_);
lean_dec_ref(v_arg_2503_);
lean_dec_ref(v_arg_2500_);
v___x_2637_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
}
}
v___jp_2492_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
v___jp_2495_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_Lean_Meta_Grind_simpForall___closed__0));
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* v_e_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* v_e_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Grind_simpExists___redArg(v_e_2646_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* v_e_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_Grind_simpExists(v_e_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_(){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2685_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
v___x_2686_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2683_, v___x_2684_, v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11____boxed(lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_();
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* v_s_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_));
v___x_2694_ = 1;
v___x_2695_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2689_, v___x_2693_, v___x_2694_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_11_));
v___x_2698_ = l_Lean_Meta_Simp_Simprocs_add(v_a_2696_, v___x_2697_, v___x_2694_, v_a_2690_, v_a_2691_);
return v___x_2698_;
}
else
{
return v___x_2695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* v_s_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Meta_Grind_addForallSimproc(v_s_2699_, v_a_2700_, v_a_2701_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
return v_res_2703_;
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
res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_995123308____hygCtx___hyg_12_();
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
